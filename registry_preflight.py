#!/usr/bin/env python3
"""Registry metadata preflight — synthetic lab, read-only, Python standard library only.

Purpose: for the five container images that Supabase CLI 2.122.1 uses for a minimal local stack, resolve and verify
registry METADATA ONLY (tag manifest / index, the linux/amd64 manifest, the image config blob) from the official
registries, hash-check every byte received, and compare the sources. No layer blob is ever requested, nothing is
pulled into Docker, no container runs, no credentials are used (anonymous pull tokens only, never printed).

Network policy (enforced in code before any connection is opened):
  * HTTPS on port 443 only; certificate verification on; no proxies.
  * Direct requests only to the registry API host and its token host listed in REGISTRIES.
  * Redirects are refused for token and manifest requests. For config-blob requests a redirect is followed only to a
    host on that registry's blob-redirect allowlist, at most 2 hops, over HTTPS, and WITHOUT the Authorization header.
  * Response size caps: manifests 4 MiB, configs 1 MiB, tokens 64 KiB. Request budget: 150 for the whole run.

Order and fail-fast: phase 1 verifies the ECR primary for all five images; the first ECR failure stops ALL further
registry lookups (remaining images: NOT_ATTEMPTED) and the result is BLOCKED. Phase 2 checks the other registries.
Reaching the request budget also stops all lookups (BLOCKED).

Docker-Content-Digest: optional in the OCI distribution spec. The authority is always the SHA-256 computed from the
received bytes; a by-digest request must hash to the requested digest. If the header is present it must match (else
INVALID); if absent it is recorded as "absent" and never reported as a match. Absence does not change the verdict.

Reporting: ECR primary verification is reported separately from cross-registry equivalence. Same-publisher sources
(GHCR; Docker Hub supabase/*) decide equivalence; upstream images (postgrest/postgrest, library/kong) are reported for
information only. No lock file is created.

Verdict (exit code): PASS 0 / PARTIAL 3 / BLOCKED 10. A PASS proves registry metadata verification only.
Output: Markdown + JSON written to $GITHUB_STEP_SUMMARY (if set) and stdout. No files, artifacts or caches.
"""
import hashlib
import http.client
import json
import os
import re
import socket
import ssl
import sys
import time
import urllib.parse

# ----------------------------------------------------------------------------------------------- what is checked
# (display name, tag, ECR repo, GHCR repo, [(Docker Hub repo, role)])   role: "same-publisher" or "upstream-info"
IMAGES = [
    ("postgres", "17.11.0.006", "supabase/postgres", "supabase/postgres", [("supabase/postgres", "same-publisher")]),
    ("gotrue", "v2.197.0", "supabase/gotrue", "supabase/gotrue", [("supabase/gotrue", "same-publisher")]),
    ("storage-api", "v1.84.19", "supabase/storage-api", "supabase/storage-api", [("supabase/storage-api", "same-publisher")]),
    ("postgrest", "v16.5", "supabase/postgrest", "supabase/postgrest", [("postgrest/postgrest", "upstream-info")]),
    ("kong", "2.8.1", "supabase/kong", "supabase/kong", [("library/kong", "upstream-info")]),
]

REGISTRIES = {
    "ecr": {
        "api": "public.ecr.aws",
        "token": "https://public.ecr.aws/token/?scope=repository:{repo}:pull",
        "redirect_exact": set(),
        # ECR Public serves blobs through AWS-managed CloudFront / S3; the concrete host is not documented.
        "redirect_patterns": [r"^d[a-z0-9]{12,14}\.cloudfront\.net$",
                              r"^prod-[a-z0-9-]+-starport-layer-bucket\.s3\.[a-z0-9-]+\.amazonaws\.com$"],
    },
    "ghcr": {
        "api": "ghcr.io",
        "token": "https://ghcr.io/token?scope=repository:{repo}:pull",
        "redirect_exact": {"pkg-containers.githubusercontent.com"},
        "redirect_patterns": [],
    },
    "dockerhub": {
        "api": "registry-1.docker.io",
        "token": "https://auth.docker.io/token?service=registry.docker.io&scope=repository:{repo}:pull",
        "redirect_exact": {"production.cloudflare.docker.com", "production.cloudfront.docker.com",
                           "docker-images-prod.6aa30f8b08e16409b46e0173d6de2f56.r2.cloudflarestorage.com"},
        "redirect_patterns": [],
    },
}

INDEX_TYPES = {"application/vnd.oci.image.index.v1+json", "application/vnd.docker.distribution.manifest.list.v2+json"}
MANIFEST_TYPES = {"application/vnd.oci.image.manifest.v1+json", "application/vnd.docker.distribution.manifest.v2+json"}
CONFIG_TYPES = {"application/vnd.oci.image.config.v1+json", "application/vnd.docker.container.image.v1+json"}
DIGEST_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
CAP_MANIFEST, CAP_CONFIG, CAP_TOKEN = 4 << 20, 1 << 20, 64 << 10
REQUEST_BUDGET = 150
TIMEOUT_S = 20


class PolicyError(Exception):
    """A request or response violated the network/format policy (never retried)."""


class Refused(PolicyError):
    """A redirect or host was refused by the allowlist (the target was never contacted)."""


class Abort(PolicyError):
    """Run-wide stop (request budget reached): no further registry lookups."""


class Unavailable(Exception):
    """The source could not be read (HTTP 401/403/404/429, network error)."""


# ----------------------------------------------------------------------------------------------- transport
_requests_made = 0
_hosts_contacted = set()


def raw_get(host, path, headers, cap):
    """One HTTPS GET to host:443 with certificate verification, no proxy, no automatic redirects.
    Returns (status, lower-cased headers dict, body bytes). Replaced by a fake transport in offline tests."""
    conn = http.client.HTTPSConnection(host, 443, timeout=TIMEOUT_S, context=ssl.create_default_context())
    try:
        conn.request("GET", path, headers=headers)
        resp = conn.getresponse()
        body = resp.read(cap + 1)
        return resp.status, {k.lower(): v for k, v in resp.getheaders()}, body
    finally:
        conn.close()


def _split(url):
    u = urllib.parse.urlsplit(url)
    if u.scheme != "https" or u.port not in (None, 443) or u.username or u.password or not u.hostname:
        raise PolicyError("non-https or non-default-port URL refused")
    path = u.path or "/"
    if u.query:
        path += "?" + u.query
    return u.hostname.lower(), path


def _get(url, allowed_hosts, headers, cap):
    """GET with host allowlist, request budget and limited retries (network errors and 5xx only)."""
    global _requests_made
    host, path = _split(url)
    if host not in allowed_hosts:
        raise Refused("host not on allowlist: " + host)
    hdrs = dict(headers)
    hdrs["User-Agent"] = "registry-metadata-preflight/1"
    hdrs["Accept-Encoding"] = "identity"
    last = None
    for attempt in range(3):
        if _requests_made >= REQUEST_BUDGET:
            raise Abort("request budget exhausted")
        _requests_made += 1
        _hosts_contacted.add(host)
        try:
            status, rh, body = raw_get(host, path, hdrs, cap)
        except (OSError, socket.timeout, http.client.HTTPException, ssl.SSLError) as e:
            last = Unavailable("network error: " + type(e).__name__)
            time.sleep(2)
            continue
        if status >= 500:
            last = Unavailable("HTTP %d" % status)
            time.sleep(2)
            continue
        if len(body) > cap:
            raise PolicyError("response exceeds size cap")
        return status, rh, body
    raise last


def fetch_token(reg, repo):
    url = REGISTRIES[reg]["token"].format(repo=repo)
    status, _, body = _get(url, {_split(url)[0]}, {"Accept": "application/json"}, CAP_TOKEN)
    if status in (301, 302, 303, 307, 308):
        raise Refused("redirect on token request refused")
    if status != 200:
        raise Unavailable("token HTTP %d" % status)
    try:
        tok = json.loads(body).get("token") or json.loads(body).get("access_token")
    except ValueError:
        raise PolicyError("token response is not JSON")
    if not isinstance(tok, str) or not tok:
        raise Unavailable("no anonymous token")
    return tok


def fetch_manifest(reg, repo, ref, token):
    api = REGISTRIES[reg]["api"]
    url = "https://%s/v2/%s/manifests/%s" % (api, repo, ref)
    accept = ", ".join(sorted(INDEX_TYPES | MANIFEST_TYPES))
    status, rh, body = _get(url, {api}, {"Accept": accept, "Authorization": "Bearer " + token}, CAP_MANIFEST)
    if status in (301, 302, 303, 307, 308):
        raise Refused("redirect on manifest request refused")
    if status in (401, 403, 404, 429):
        raise Unavailable("manifest HTTP %d" % status)
    if status != 200:
        raise PolicyError("unexpected manifest HTTP %d" % status)
    digest = "sha256:" + hashlib.sha256(body).hexdigest()
    hdr = rh.get("docker-content-digest")
    if hdr is None:
        hdr_state = "absent"
    elif hdr == digest:
        hdr_state = "present-match"
    else:
        raise PolicyError("Docker-Content-Digest header does not match the received bytes")
    if DIGEST_RE.match(ref) and ref != digest:
        raise PolicyError("manifest bytes do not match the requested digest")
    ctype = (rh.get("content-type") or "").split(";")[0].strip()
    try:
        doc = json.loads(body)
    except ValueError:
        raise PolicyError("manifest is not JSON")
    mt = doc.get("mediaType") or ctype
    if mt not in INDEX_TYPES | MANIFEST_TYPES or (doc.get("mediaType") and ctype and ctype != doc["mediaType"]):
        raise PolicyError("unexpected or inconsistent manifest media type")
    return digest, mt, doc, hdr_state


def fetch_config(reg, repo, desc, token):
    api = REGISTRIES[reg]["api"]
    digest, size = desc.get("digest"), desc.get("size")
    if not (isinstance(digest, str) and DIGEST_RE.match(digest)) or not isinstance(size, int) or not 0 < size <= CAP_CONFIG:
        raise PolicyError("config descriptor invalid or too large")
    url = "https://%s/v2/%s/blobs/%s" % (api, repo, digest)
    status, rh, body = _get(url, {api}, {"Authorization": "Bearer " + token}, CAP_CONFIG)
    hops, via = 0, []
    while status in (301, 302, 303, 307, 308):
        hops += 1
        if hops > 2:
            raise Refused("too many redirects")
        loc = rh.get("location") or ""
        nxt = urllib.parse.urljoin(url, loc)
        try:
            host, _ = _split(nxt)                               # https/port check
        except PolicyError as e:
            raise Refused("blob redirect refused: " + str(e))
        cfg = REGISTRIES[reg]
        if host not in cfg["redirect_exact"] and not any(re.match(p, host) for p in cfg["redirect_patterns"]):
            raise Refused("blob redirect to non-allowlisted host refused: " + host)
        via.append(host)
        url = nxt
        status, rh, body = _get(url, {host}, {}, CAP_CONFIG)  # no Authorization to the storage host
    if status in (401, 403, 404, 429):
        raise Unavailable("config HTTP %d" % status)
    if status != 200:
        raise PolicyError("unexpected config HTTP %d" % status)
    if len(body) != size or "sha256:" + hashlib.sha256(body).hexdigest() != digest:
        raise PolicyError("config bytes do not match the descriptor digest/size")
    try:
        cfgdoc = json.loads(body)
    except ValueError:
        raise PolicyError("config is not JSON")
    return cfgdoc, via


def canon(obj):
    return hashlib.sha256(json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def resolve(reg, repo, tag):
    """Return a verified record for one image in one registry, or raise PolicyError / Unavailable."""
    token = fetch_token(reg, repo)
    top_digest, top_type, top, top_hdr = fetch_manifest(reg, repo, tag, token)
    if top_type in INDEX_TYPES:
        cands = []
        for d in top.get("manifests") or []:
            p = d.get("platform") or {}
            ann = d.get("annotations") or {}
            if ann.get("vnd.docker.reference.type") == "attestation-manifest":
                continue
            if p.get("os") == "linux" and p.get("architecture") == "amd64" and not p.get("variant"):
                cands.append(d)
        if len(cands) != 1:
            raise PolicyError("index has %d linux/amd64 entries (exactly 1 required)" % len(cands))
        pm_digest = cands[0].get("digest")
        if not (isinstance(pm_digest, str) and DIGEST_RE.match(pm_digest)) or cands[0].get("mediaType") not in MANIFEST_TYPES:
            raise PolicyError("invalid linux/amd64 descriptor")
        pm_digest2, pm_type, pm, pm_hdr = fetch_manifest(reg, repo, pm_digest, token)
        if pm_type not in MANIFEST_TYPES or pm_digest2 != pm_digest:
            raise PolicyError("platform manifest invalid")
        kind = "index"
    else:
        pm_digest, pm, pm_hdr = top_digest, top, top_hdr
        kind = "single-manifest"
    if pm.get("schemaVersion") != 2:
        raise PolicyError("manifest schemaVersion must be 2")
    cdesc = pm.get("config") or {}
    if cdesc.get("mediaType") not in CONFIG_TYPES:
        raise PolicyError("unexpected config media type")
    layers = pm.get("layers") or []
    for l in layers:
        if not (isinstance(l.get("digest"), str) and DIGEST_RE.match(l["digest"]) and isinstance(l.get("size"), int)):
            raise PolicyError("invalid layer descriptor")
    cfg, via = fetch_config(reg, repo, cdesc, token)
    if cfg.get("os") != "linux" or cfg.get("architecture") != "amd64":
        raise PolicyError("config platform is not linux/amd64")
    rootfs = cfg.get("rootfs") or {}
    diff_ids = rootfs.get("diff_ids") or []
    if rootfs.get("type") != "layers" or len(diff_ids) != len(layers) or not all(DIGEST_RE.match(x or "") for x in diff_ids):
        raise PolicyError("rootfs.diff_ids inconsistent with manifest layers")
    return {
        "registry": reg, "repo": repo, "tag": tag, "tag_resolves_to": kind,
        "tag_digest": top_digest, "linux_amd64_manifest_digest": pm_digest, "config_digest": cdesc["digest"],
        "digest_header_tag": top_hdr, "digest_header_platform_manifest": pm_hdr,
        "layer_digests": [l["digest"] for l in layers], "layer_count": len(layers),
        "diff_ids_sha256": canon(diff_ids), "runtime_config_sha256": canon(cfg.get("config") or {}),
        "_diff_ids": diff_ids, "_runtime": cfg.get("config") or {}, "_cfg_top": {k: cfg.get(k) for k in ("created", "author", "history")},
        "blob_redirect_hosts": via,
    }


def compare(a, b):
    """IDENTICAL: same config digest (config bytes identical, so diff_ids and runtime config identical).
    MATERIAL_MISMATCH: platform, diff_ids or runtime configuration differ.
    NEEDS_REVIEW: config digests differ although platform, diff_ids and runtime configuration match (e.g. build
    metadata such as created/history); reported, never auto-accepted."""
    if a["config_digest"] == b["config_digest"]:
        note = "layer blobs identical" if a["layer_digests"] == b["layer_digests"] else "layer blob digests differ (same diff_ids)"
        return "IDENTICAL", note
    diffs = []
    if a["_diff_ids"] != b["_diff_ids"]:
        diffs.append("rootfs.diff_ids")
    if a["_runtime"] != b["_runtime"]:
        keys = sorted(set(a["_runtime"]) | set(b["_runtime"]))
        diffs.append("runtime config: " + ",".join(k for k in keys if a["_runtime"].get(k) != b["_runtime"].get(k)))
    if diffs:
        return "MATERIAL_MISMATCH", "; ".join(diffs)
    other = [k for k in ("created", "author", "history") if a["_cfg_top"].get(k) != b["_cfg_top"].get(k)]
    return "NEEDS_REVIEW", "config differs only in: " + (",".join(other) or "other config fields")


# ----------------------------------------------------------------------------------------------- run
def _attempt(reg, repo, role, tag):
    """Resolve one source; returns (entry, record-or-None). Abort propagates (run-wide stop)."""
    entry = {"registry": reg, "repo": repo, "role": role}
    try:
        r = resolve(reg, repo, tag)
        entry.update(status="OK", **{k: v for k, v in r.items() if not k.startswith("_")})
        return entry, r
    except Abort:
        raise
    except Refused as e:
        entry.update(status="REFUSED", detail=str(e))
    except PolicyError as e:
        entry.update(status="INVALID", detail=str(e))
    except Unavailable as e:
        entry.update(status="UNAVAILABLE", detail=str(e))
    return entry, None


def run():
    recs = []
    for name, tag, ecr_repo, ghcr_repo, dh in IMAGES:
        others = [("ghcr", ghcr_repo, "same-publisher")] + [("dockerhub", r, role) for r, role in dh]
        recs.append({"image": name, "tag": tag, "ecr": None, "ecr_verification": "NOT_ATTEMPTED", "_others": others,
                     "same_publisher": [], "upstream_info": [], "equivalence": "NOT_ATTEMPTED",
                     "verdict": "BLOCKED", "reason": "not attempted (fail-fast)"})
    primaries, stop = {}, None
    # phase 1 — ECR primary for every image; the first failure stops all further lookups
    for rec in recs:
        repo = next(i[2] for i in IMAGES if i[0] == rec["image"])
        try:
            entry, r = _attempt("ecr", repo, "primary", rec["tag"])
        except Abort as e:
            stop = "run stopped: " + str(e)
            break
        rec["ecr"] = entry
        if r is None:
            rec["ecr_verification"] = "FAILED"
            rec["reason"] = "ECR primary not verified: %s" % entry.get("detail")
            stop = "fail-fast after ECR failure for %s" % rec["image"]
            break
        rec["ecr_verification"] = "VERIFIED"
        primaries[rec["image"]] = r
    # phase 2 — other registries (only if every primary verified)
    if stop is None:
        for rec in recs:
            primary = primaries[rec["image"]]
            identical, review, material = 0, [], []
            for reg, repo, role in rec["_others"]:
                try:
                    entry, other = _attempt(reg, repo, role, rec["tag"])
                except Abort as e:
                    stop = "run stopped: " + str(e)
                    break
                item = {"source": entry}
                if other is not None:
                    c, note = compare(primary, other)
                    item.update(result=c, note=note)
                else:
                    item.update(result="NOT_COMPARED", note=entry["status"] + ": " + str(entry.get("detail")))
                if role != "same-publisher":
                    rec["upstream_info"].append(item)
                    continue
                rec["same_publisher"].append(item)
                if other is None:
                    if entry["status"] == "INVALID":
                        material.append("%s/%s invalid: %s" % (reg, repo, entry.get("detail")))
                elif item["result"] == "IDENTICAL":
                    identical += 1
                elif item["result"] == "NEEDS_REVIEW":
                    review.append("%s/%s: %s" % (reg, repo, item["note"]))
                else:
                    material.append("%s/%s: %s" % (reg, repo, item["note"]))
            if stop:
                rec["reason"] = stop
                break
            if material:
                rec["equivalence"], rec["verdict"] = "MATERIAL_MISMATCH", "BLOCKED"
                rec["reason"] = "same-publisher mismatch: " + " | ".join(material)
            elif identical:
                rec["equivalence"], rec["verdict"] = "IDENTICAL_SAME_PUBLISHER", "PASS"
                rec["reason"] = "%d same-publisher source(s) with identical config" % identical
            elif review:
                rec["equivalence"], rec["verdict"] = "NEEDS_REVIEW", "PARTIAL"
                rec["reason"] = "differences need manual review: " + " | ".join(review)
            else:
                rec["equivalence"], rec["verdict"] = "NO_SECOND_SOURCE", "PARTIAL"
                rec["reason"] = "ECR verified; no same-publisher source available for comparison"
    for rec in recs:
        rec.pop("_others", None)
    overall = "BLOCKED" if stop or any(r["verdict"] == "BLOCKED" for r in recs) else (
        "PARTIAL" if any(r["verdict"] == "PARTIAL" for r in recs) else "PASS")
    return overall, recs, stop


def _row(img, s):
    return "| %s | %s %s (%s) | %s | %s | %s | %s | %s/%s | %s |" % (
        img, s["registry"], s["repo"], s["role"], s["status"] + (": " + s["detail"] if s.get("detail") else ""),
        s.get("tag_digest", ""), s.get("linux_amd64_manifest_digest", ""), s.get("config_digest", ""),
        s.get("digest_header_tag", "-"), s.get("digest_header_platform_manifest", "-"), s.get("layer_count", ""))


def render(overall, results, started, stop):
    hdr = "| image | source | status | tag digest | linux/amd64 manifest | config | Docker-Content-Digest (tag/platform) | layers |"
    sep = "|---|---|---|---|---|---|---|---|"
    out = ["# Registry metadata preflight — synthetic lab", "",
           "Overall verdict: %s (metadata verification only; authorizes nothing else)" % overall,
           "Started (UTC): %s · requests: %d · hosts contacted: %s" % (started, _requests_made, ", ".join(sorted(_hosts_contacted)) or "none"),
           "Stop: %s" % (stop or "none"), "",
           "## 1. ECR primary verification (independent of cross-registry equivalence)",
           "ECR verified: %d/%d" % (sum(r["ecr_verification"] == "VERIFIED" for r in results), len(results)), "", hdr, sep]
    for r in results:
        out.append(_row(r["image"], r["ecr"]) if r["ecr"] else "| %s | ecr | %s | | | | | |" % (r["image"], r["ecr_verification"]))
    out += ["", "## 2. Same-publisher equivalence (decides PASS)", "",
            "| image | equivalence | comparison | result | note |", "|---|---|---|---|---|"]
    for r in results:
        for i in r["same_publisher"] or [{"source": {"registry": "-", "repo": "-"}, "result": "-", "note": "-"}]:
            out.append("| %s | %s | ECR vs %s/%s | %s | %s |" % (r["image"], r["equivalence"], i["source"]["registry"], i["source"]["repo"], i["result"], i["note"]))
    out += ["", hdr, sep] + [_row(r["image"], i["source"]) for r in results for i in r["same_publisher"]]
    out += ["", "## 3. Upstream images (information only; never decide the verdict)", "",
            "| image | comparison | result | note |", "|---|---|---|---|"]
    out += ["| %s | ECR vs %s/%s | %s | %s |" % (r["image"], i["source"]["registry"], i["source"]["repo"], i["result"], i["note"])
            for r in results for i in r["upstream_info"]]
    out += ["", "## 4. Verdict per image", "", "| image | ECR | equivalence | verdict | reason |", "|---|---|---|---|---|"]
    out += ["| %s | %s | %s | %s | %s |" % (r["image"], r["ecr_verification"], r["equivalence"], r["verdict"], r["reason"]) for r in results]
    out += ["", "CANDIDATE VALUES — NOT A LOCK (ECR-verified only; subject to independent review):", "```"]
    for r in results:
        s = r["ecr"] if r["ecr_verification"] == "VERIFIED" else None
        out.append("public.ecr.aws/%s:%s linux/amd64 %s %s %s" % (
            s["repo"], r["tag"], s["tag_digest"], s["linux_amd64_manifest_digest"], s["config_digest"]) if s else
            "%s:%s %s" % (r["image"], r["tag"], r["ecr_verification"]))
    out += ["```", "", "Machine-readable result:", "```json",
            json.dumps({"overall": overall, "stop": stop, "started_utc": started, "requests": _requests_made,
                        "hosts_contacted": sorted(_hosts_contacted), "images": results}, indent=1, sort_keys=True), "```"]
    return "\n".join(out) + "\n"


def main():
    started = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    try:
        overall, results, stop = run()
    except Exception as e:                       # any unexpected failure is BLOCKED, never PASS
        overall, results, stop = "BLOCKED", [], "internal error: " + type(e).__name__
    try:
        text = render(overall, results, started, stop)
    except Exception as e:                       # a reporting failure is BLOCKED too, never PASS
        overall = "BLOCKED"
        text = "# Registry metadata preflight — synthetic lab\n\nOverall verdict: BLOCKED (report rendering failed: %s)\n" % type(e).__name__
    sys.stdout.write(text)
    path = os.environ.get("GITHUB_STEP_SUMMARY")
    if path:
        with open(path, "a", encoding="utf-8") as f:
            f.write(text)
    return {"PASS": 0, "PARTIAL": 3}.get(overall, 10)


if __name__ == "__main__":
    sys.exit(main())
