#!/usr/bin/env python3
"""Compare source-to-world archive streaming versus selective Git blob admission.

Offline mode uses identical synthetic Lean files under both transport wrappers.
Live mode requires pinned owner/repo + exact commit. Every measured acquisition
runs the REAL archive/REST parser into SourceWorldBuilder's verified-byte sink.
No checkout, no Lean elaboration or kernel certification, no CI requirement.

  python3 scripts/bench_lean_world_acquisition.py --mode offline --files 100 1000
  python3 scripts/bench_lean_world_acquisition.py --mode live --repo owner/repo --revision 40HEX
"""
from __future__ import annotations
import argparse
import base64
import hashlib
import io
import json
import os
from pathlib import Path
import resource
import statistics
import tarfile
import time
import tracemalloc
import urllib.request

from lean_world_source_world import SourceWorldBuilder
from lean_remote_archive_stream import stream_archive, REPO_RE, COMMIT_RE
from lean_remote_source_inventory import inventory

OFFLINE_REPO = "synthetic/source-world"
OFFLINE_REV = "a"*40


class WireReader:
    def __init__(self, source):
        self.source = source
        self.bytes = 0

    def read(self, n=-1):
        chunk = self.source.read(n)
        self.bytes += len(chunk)
        return chunk


class GitAPI:
    """Deterministic REST tree/blob API fixture; exact same original files."""
    def __init__(self, members):
        self.blobs = {}
        self.entries = []
        self.wire = 0
        self.calls = 0
        for path, data in members:
            digest = hashlib.sha1(
                b"blob " + str(len(data)).encode("ascii") + b"\0" + data
            ).hexdigest()
            self.blobs[digest] = data
            self.entries.append({"type": "blob", "mode": "100644",
                                 "path": path, "sha": digest, "size": len(data)})

    def opener(self, request):
        self.calls += 1
        url = request.full_url
        if "/git/trees/" in url:
            payload = {"truncated": False, "tree": self.entries}
        elif "/git/blobs/" in url:
            data = self.blobs[url.rsplit("/", 1)[-1]]
            payload = {"encoding": "base64", "content": base64.b64encode(data).decode(),
                       "size": len(data)}
        else:
            raise ValueError("unrecognized test REST path")
        raw = json.dumps(payload).encode()
        self.wire += len(raw)
        return raw


def fixture(count: int, body_bytes: int):
    members = []
    for i in range(count):
        leading = f"theorem d{i:08d} : True := trivial\n".encode()
        body = (leading + b"-- " + b"x"*max(0, body_bytes-len(leading)-3)
                + b"\n")
        members.append((f"src/Module_{i:08d}.lean", body))
    out = io.BytesIO()
    with tarfile.open(fileobj=out, mode="w:gz") as tar:
        for path, data in members:
            info = tarfile.TarInfo("repo-root/"+path)
            info.size = len(data)
            tar.addfile(info, io.BytesIO(data))
    return members, out.getvalue()


def measure(name, reader, expected_files):
    builder = SourceWorldBuilder()
    tracemalloc.start()
    start = time.perf_counter()
    transferred, requests = reader(builder)
    elapsed = time.perf_counter()-start
    _, peak = tracemalloc.get_traced_memory()
    tracemalloc.stop()
    counts = builder.counters()
    if counts["source_occurrences"] != expected_files or counts["skipped_size_cap"]:
        raise AssertionError("acquisition incomplete or unverified")
    return {
        "transport": name,
        "source_occurrences": counts["source_occurrences"],
        "source_bytes": sum(r["size"] for r in builder.manifest()),
        "network_payload_bytes": transferred,
        "http_requests": requests,
        "wall_seconds": round(elapsed, 6),
        "source_bytes_per_second": round(
            sum(r["size"] for r in builder.manifest())/max(elapsed,1e-9)),
        "peak_tracemalloc_bytes": peak,
        "manifest_jsonl_bytes": len(builder.manifest_jsonl().encode()),
        "lean_elaboration": False, "kernel_checked": False,
    }


def offline(count, source_bytes):
    members, archive_blob = fixture(count, source_bytes)
    api = GitAPI(members)

    def archive_reader(builder):
        wire = WireReader(io.BytesIO(archive_blob))
        builder.ingest_archive(wire, OFFLINE_REPO, OFFLINE_REV)
        return wire.bytes, 1

    def rest_reader(builder):
        builder.ingest_rest(OFFLINE_REPO, OFFLINE_REV, opener=api.opener)
        return api.wire, api.calls

    return {
        "mode": "synthetic-offline-source-to-world",
        "files": count, "nominal_file_bytes": source_bytes,
        "archive": measure("archive", archive_reader, count),
        "selective_git_blobs": measure("rest-tree+blobs", rest_reader, count),
    }


def live(repo, revision, max_blob_bytes, max_total_bytes, max_transfer_bytes):
    if not REPO_RE.fullmatch(repo) or not COMMIT_RE.fullmatch(revision):
        raise ValueError("live mode requires pinned OWNER/REPO and 40-digit revision")
    safe = [urllib.parse.quote(p, safe="") for p in repo.split("/")]
    url = f"https://codeload.github.com/{safe[0]}/{safe[1]}/tar.gz/{revision}"

    def archive_reader(builder):
        request = urllib.request.Request(
            url, headers={"User-Agent":"dashi-lean-world-bench/1"})
        with urllib.request.urlopen(request, timeout=60) as response:
            wire = WireReader(response)
            builder.ingest_archive(wire, repo, revision,
                                   max_file_bytes=max_blob_bytes,
                                   max_total_bytes=max_total_bytes,
                                   max_transfer_bytes=max_transfer_bytes)
            return wire.bytes, 1

    # Preserve the same user-authenticated REST request safeguards.
    token = os.environ.get("GITHUB_TOKEN")
    api_wire = [0]
    calls = [0]
    def opener(request):
        calls[0] += 1
        with urllib.request.urlopen(request, timeout=60) as response:
            raw = response.read(64*1024*1024+1)
        api_wire[0] += len(raw)
        return raw

    def rest_reader(builder):
        builder.ingest_rest(
            repo, revision, opener=opener, token=token,
            max_blob_bytes=max_blob_bytes)
        return api_wire[0], calls[0]

    # A live first pass learns its exact source count. Repeat only when the
    # modes are COMPLETE and source origins/digests agree.
    items = []
    def collect(mode, f):
        b = SourceWorldBuilder()
        tracemalloc.start()
        started = time.perf_counter()
        transferred, requests = f(b)
        seconds = time.perf_counter()-started
        _, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        receipts = {(x["repository"], x["revision"], x["path"]):
                    (x["sha256"], x["git_blob"]) for x in b.manifest()}
        return {"transport": mode, "source_occurrences": len(receipts),
                "source_bytes": sum(x["size"] for x in b.manifest()),
                "wire_bytes": transferred, "requests": requests,
                "seconds": seconds, "peak_python_bytes": peak,
                "skipped": b.skipped}, receipts
    a, left = collect("archive", archive_reader)
    b, right = collect("REST-tree+blobs", rest_reader)
    if a["skipped"] or b["skipped"] or left != right:
        raise RuntimeError("live acquisition modes not identical and complete")
    return {"mode":"live-source-to-world-not-lean",
            "repo":repo,"revision":revision,
            "archive":a,"selective_git_blobs":b}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--mode", choices=["offline","live"], default="offline")
    p.add_argument("--files", nargs="+", type=int, default=[100,1000])
    p.add_argument("--source-bytes", type=int, default=1024)
    p.add_argument("--repo")
    p.add_argument("--revision")
    p.add_argument("--max-blob-bytes", type=int, default=8*1024*1024)
    p.add_argument("--max-total-bytes", type=int, default=4*1024*1024*1024)
    p.add_argument("--max-transfer-bytes", type=int, default=2*1024*1024*1024)
    args=p.parse_args()
    if args.mode=="offline":
        if any(n<1 for n in args.files) or args.source_bytes<32:
            p.error("positive file counts and source bytes >= 32 required")
        rows=[offline(n,args.source_bytes) for n in args.files]
    else:
        if not args.repo or not args.revision:
            p.error("live mode requires --repo and --revision")
        rows=[live(args.repo,args.revision,args.max_blob_bytes,
                   args.max_total_bytes,args.max_transfer_bytes)]
    print(json.dumps({"runs":rows},indent=2,sort_keys=True))


if __name__=="__main__":
    import urllib.parse
    main()
