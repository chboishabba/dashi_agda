#!/usr/bin/env python3
"""Stream a pinned public GitHub repository tarball without checkout or disk writes.

This is a source-inventory tool, not a Lean elaborator. It makes one streaming
archive HTTP request per repository instead of one API blob request per file.
Never extracts the tar archive to the filesystem. Processing is bounded by
per-file and total uncompressed byte limits. Explicitly reports excluded files.
For private repositories use authenticated blob API mode, not this public mode.

Usage:
  python3 scripts/lean_remote_archive_stream.py OWNER/REPO 40_HEX_SHA
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import tarfile
import urllib.parse
import urllib.request
from typing import BinaryIO, Iterator

REPO_RE = re.compile(r"^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$")
COMMIT_RE = re.compile(r"^[0-9a-fA-F]{40}$")


class ArchiveError(RuntimeError):
    pass


def stream_archive(fileobj: BinaryIO, repo: str, revision: str,
                   *, max_file_bytes: int = 8 * 1024 * 1024,
                   max_total_bytes: int = 4 * 1024 * 1024 * 1024) -> Iterator[dict]:
    """Process tar.gz sequentially; source bytes never hit the filesystem."""
    if not REPO_RE.fullmatch(repo) or not COMMIT_RE.fullmatch(revision):
        raise ValueError("repo and immutable revision required")
    if min(max_file_bytes, max_total_bytes) < 0:
        raise ValueError("negative size cap")
    total = 0
    with tarfile.open(fileobj=fileobj, mode="r|gz") as archive:
        prefix = None
        for member in archive:
            # Ignore non-regular files. No archive extraction is ever performed.
            if not member.isfile():
                continue
            path = member.name
            if prefix is None:
                prefix = path.split("/", 1)[0]
            if not path.startswith(prefix + "/"):
                raise ArchiveError("archive unexpectedly changed root")
            relative = path[len(prefix) + 1:]
            if not relative.endswith(".lean"):
                continue
            if (not relative or relative.startswith("/") or "\\x00" in relative
                    or any(segment in ("", ".", "..") for segment in relative.split("/"))):
                raise ArchiveError("unsafe archive member path")
            if member.size < 0:
                raise ArchiveError("invalid archive member length")
            if member.size > max_total_bytes - total:
                raise ArchiveError("archive exceeds total Lean source byte budget")
            total += member.size
            if member.size > max_file_bytes:
                yield {"kind": "lean-source", "repository": repo, "revision": revision,
                       "path": relative, "size": member.size, "status": "skipped-size-cap"}
                continue
            src = archive.extractfile(member)
            if src is None:
                raise ArchiveError("cannot read source member")
            sha256 = hashlib.sha256()
            git_sha1 = hashlib.sha1()
            git_sha1.update(b"blob " + str(member.size).encode("ascii") + bytes([0]))
            remaining = member.size
            while remaining:
                chunk = src.read(min(65536, remaining))
                if not chunk:
                    raise ArchiveError("archive member truncated")
                sha256.update(chunk)
                git_sha1.update(chunk)
                remaining -= len(chunk)
            yield {"kind": "lean-source", "repository": repo, "revision": revision,
                   "path": relative, "size": member.size,
                   "git_blob": git_sha1.hexdigest(), "sha256": sha256.hexdigest(),
                   "status": "source-verified-not-elaborated"}


def run(repo: str, revision: str, *, max_file_bytes: int,
        max_total_bytes: int) -> Iterator[dict]:
    if not REPO_RE.fullmatch(repo) or not COMMIT_RE.fullmatch(revision):
        raise ValueError("expected OWNER/REPO and immutable 40-character commit")
    owner, name = repo.split("/")
    url = ("https://codeload.github.com/"
           + urllib.parse.quote(owner, safe="") + "/"
           + urllib.parse.quote(name, safe="") + "/tar.gz/" + revision)
    req = urllib.request.Request(url, headers={"User-Agent": "dashi-lean-world-stream/1"})
    with urllib.request.urlopen(req, timeout=60) as resp:
        yield from stream_archive(resp, repo, revision,
                                  max_file_bytes=max_file_bytes,
                                  max_total_bytes=max_total_bytes)


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("repository")
    p.add_argument("revision")
    p.add_argument("--max-file-bytes", type=int, default=8 * 1024 * 1024)
    p.add_argument("--max-total-bytes", type=int, default=4 * 1024 * 1024 * 1024)
    args = p.parse_args()
    try:
        for item in run(args.repository, args.revision,
                        max_file_bytes=args.max_file_bytes,
                        max_total_bytes=args.max_total_bytes):
            print(json.dumps(item, sort_keys=True), flush=True)
        return 0
    except (ValueError, ArchiveError, OSError, tarfile.TarError) as exc:
        print(f"ARCHIVE_INCOMPLETE: {type(exc).__name__}: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
