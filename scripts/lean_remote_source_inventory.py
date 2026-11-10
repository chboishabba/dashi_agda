#!/usr/bin/env python3
"""Zero-checkout GitHub Lean source inventory, pinned to an immutable commit.

No repository clone, temporary checkout, or source file is written. This tool
fetches remote tree metadata and one source blob at a time and emits only
provenance, size and hashes as JSONL. It is NOT a Lean elaborator or proof
checker. Source bytes exist transiently in memory to compute their digest.

Usage:
  python3 scripts/lean_remote_source_inventory.py OWNER/REPO COMMIT_SHA > world.jsonl
  python3 scripts/lean_remote_source_inventory.py OWNER/REPO COMMIT_SHA --max-blob-bytes 1048576
Auth: GITHUB_TOKEN environment variable (optional); token is never printed.
"""
from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
import re
import sys
import urllib.error
import urllib.parse
import urllib.request
from typing import Callable

COMMIT_RE = re.compile(r"^[a-fA-F0-9]{40}$")
REPO_RE = re.compile(r"^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$")
SHA_RE = re.compile(r"^[a-fA-F0-9]{40}$")
DEFAULT_MAX_BLOB = 8 * 1024 * 1024


class RemoteError(RuntimeError):
    pass


def request_json(url: str, *, token: str | None = None,
                 opener: Callable | None = None) -> dict:
    """Use authenticated GitHub REST API with explicit timeout and error checks."""
    headers = {"Accept": "application/vnd.github+json",
               "User-Agent": "dashi-lean-world-zero-checkout/1",
               "X-GitHub-Api-Version": "2022-11-28"}
    if token:
        headers["Authorization"] = f"Bearer {token}"
    request = urllib.request.Request(url, headers=headers)
    try:
        if opener:
            data = opener(request)
        else:
            with urllib.request.urlopen(request, timeout=30) as response:
                # cap remote JSON response size; fail closed, never truncate silently
                data = response.read(64 * 1024 * 1024 + 1)
        if len(data) > 64 * 1024 * 1024:
            raise RemoteError("API response exceeds 64MiB cap")
        obj = json.loads(data)
    except (urllib.error.HTTPError, urllib.error.URLError, TimeoutError,
            ValueError) as exc:
        raise RemoteError(f"remote metadata request failed ({type(exc).__name__})") from exc
    if not isinstance(obj, dict):
        raise RemoteError("unexpected GitHub JSON object")
    return obj


def repository_tree(repo: str, commit: str, *, token: str | None = None,
                    opener: Callable | None = None) -> list[dict]:
    if not REPO_RE.fullmatch(repo) or not COMMIT_RE.fullmatch(commit):
        raise ValueError("expected OWNER/REPO and immutable 40-digit commit SHA")
    safe_repo = "/".join(urllib.parse.quote(part, safe="") for part in repo.split("/"))
    url = f"https://api.github.com/repos/{safe_repo}/git/trees/{commit}?recursive=1"
    tree = request_json(url, token=token, opener=opener)
    if tree.get("truncated") is not False:
        raise RemoteError("tree response missing explicit non-truncated coverage")
    items = tree.get("tree")
    if not isinstance(items, list):
        raise RemoteError("invalid Git tree response")
    filtered = []
    for item in items:
        if (not isinstance(item, dict) or item.get("type") != "blob"
                or item.get("mode") not in ("100644", "100755")):
            continue   # exclude submodules, symlinks, directories
        path, sha, size = item.get("path"), item.get("sha"), item.get("size")
        if (not isinstance(path, str) or not path.endswith(".lean")
                or path.startswith("/") or chr(0) in path
                or any(part in ("", ".", "..") for part in path.split("/"))
                or not isinstance(sha, str) or not SHA_RE.fullmatch(sha)
                or type(size) is not int or size < 0):
            raise RemoteError("invalid or unsafe source tree entry")
        filtered.append({"path": path, "sha": sha.lower(), "size": size})
    return sorted(filtered, key=lambda x: x["path"])


def source_blob(repo: str, blob_sha: str, max_size: int,
                *, token: str | None = None, opener: Callable | None = None) -> bytes:
    if not REPO_RE.fullmatch(repo) or not SHA_RE.fullmatch(blob_sha):
        raise ValueError("bad repository or blob SHA")
    if max_size < 0:
        raise ValueError("negative size cap")
    safe_repo = "/".join(urllib.parse.quote(part, safe="") for part in repo.split("/"))
    url = f"https://api.github.com/repos/{safe_repo}/git/blobs/{blob_sha}"
    obj = request_json(url, token=token, opener=opener)
    if obj.get("encoding") != "base64" or not isinstance(obj.get("content"), str):
        raise RemoteError("unsupported blob encoding")
    declared = obj.get("size")
    if type(declared) is not int or declared < 0 or declared > max_size:
        raise RemoteError("blob exceeds permitted bound")
    # Avoid attempting unbounded base64 allocation.
    if len(obj["content"]) > 4 * ((max_size + 2) // 3) + 8192:
        raise RemoteError("base64 payload exceeds permitted bound")
    try:
        data = base64.b64decode(obj["content"], validate=False)
    except (ValueError, base64.binascii.Error) as exc:
        raise RemoteError("invalid base64 source") from exc
    if len(data) != declared or len(data) > max_size:
        raise RemoteError("blob content size mismatch")
    # Verify Git blob object identity, not merely the HTTP response's claimed SHA.
    git_hash = hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + bytes([0]) + data).hexdigest()
    if git_hash != blob_sha.lower():
        raise RemoteError("source does not match requested Git object SHA-1")
    return data


def inventory(repo: str, commit: str, *, max_blob_bytes: int = DEFAULT_MAX_BLOB,
              token: str | None = None, opener: Callable | None = None,
              on_source: Callable[[dict, bytes], None] | None = None):
    """Yield source metadata; never write a repo tree or source blob to disk."""
    for item in repository_tree(repo, commit, token=token, opener=opener):
        if item["size"] > max_blob_bytes:
            yield {"kind": "lean-source", "repository": repo, "revision": commit,
                   "path": item["path"], "git_blob": item["sha"],
                   "size": item["size"], "status": "skipped-size-cap"}
            continue
        raw = source_blob(repo, item["sha"], max_blob_bytes,
                          token=token, opener=opener)
        receipt = {"kind": "lean-source", "repository": repo,
                   "revision": commit, "path": item["path"],
                   "git_blob": item["sha"], "size": len(raw),
                   "sha256": hashlib.sha256(raw).hexdigest(),
                   "status": "source-verified-not-elaborated"}
        if on_source is not None:
            # Bytes are transient, hash-checked and cap-bounded. No checkout,
            # and no source content is embedded in ordinary JSONL inventory.
            on_source(receipt, raw)
        yield receipt


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repository", help="GitHub OWNER/REPO")
    parser.add_argument("revision", help="exact 40-digit commit SHA")
    parser.add_argument("--max-blob-bytes", type=int, default=DEFAULT_MAX_BLOB)
    args = parser.parse_args()
    try:
        for item in inventory(args.repository, args.revision,
                              max_blob_bytes=args.max_blob_bytes,
                              token=os.environ.get("GITHUB_TOKEN")):
            print(json.dumps(item, sort_keys=True), flush=True)
    except (RemoteError, ValueError) as exc:
        print(f"REMOTE_INVENTORY_INCOMPLETE: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
