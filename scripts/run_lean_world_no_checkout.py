#!/usr/bin/env python3
"""Original source-pinned GitHub Lean world intake without repo checkout.

SOURCE MODE: verified bytes -> source-world provenance occurrences.
COMPILE MODE: source callback -> pinned Nix Lean compiler and shared OLean
cache, returning a compile receipt only. This does not export kernel terms,
declare theorem identity or certify a theorem. Source/exact/proof admission
is deliberately separate.

Run (source only):
  python3 scripts/run_lean_world_no_checkout.py owner/repo 40SHA --transport archive
Run (actual pinned Nix shell + compiled dep closure):
  python3 scripts/run_lean_world_no_checkout.py owner/repo 40SHA --transport rest \
    --compile --flake . --cache /path/to/lean-olean-cache \
    --closure-digest 64HEX [--dependency-oleans /path/to/pinned/compiled]

Never writes a clone or source tree; ephemeral Lean compilation materializes
only one bounded module in a TemporaryDirectory, then removes it.
"""
from __future__ import annotations
import argparse
from dataclasses import asdict
import json
from pathlib import Path
import os
import sys
import tracemalloc
import time

from lean_world_source_world import SourceWorldBuilder
from lean_ephemeral_elaboration import (
    EphemeralLeanWorker, compiled_dependency_digest, ElaborationError)
from lean_remote_archive_stream import (
    run as archive_run, REPO_RE, COMMIT_RE)
from lean_remote_source_inventory import inventory as rest_inventory


def ingest(repository: str, revision: str, *, transport: str,
           compiler: EphemeralLeanWorker | None,
           max_blob_bytes: int, max_total_bytes: int,
           max_transfer_bytes: int):
    processing=[]
    def on_source(receipt, raw):
        if compiler is None:
            processing.append({"kind":"source-admitted-not-elaborated",
                               "repository":receipt["repository"],
                               "revision":receipt["revision"],
                               "path":receipt["path"], "sha256":receipt["sha256"]})
        else:
            # Absolute module filename is not accepted by worker.
            result=compiler.elaborate(receipt,raw,receipt["path"])
            processing.append({
                "kind":"lean-source-compilation",
                "repository":receipt["repository"],"revision":receipt["revision"],
                "path":receipt["path"], **asdict(result)})
    builder=SourceWorldBuilder(consumer=on_source)
    start=time.perf_counter()
    tracemalloc.start()
    if transport=="rest":
        for row in rest_inventory(
                repository, revision, max_blob_bytes=max_blob_bytes,
                token=os.environ.get("GITHUB_TOKEN"), on_source=builder.admit):
            if row["status"]=="skipped-size-cap":
                builder.skip(row)
    else:
        # Use archive.run's validated public one-request HTTPS transport.
        # archive.run does not yet pass a callback, so open a bounded
        # streaming response here and pass its raw stream to source builder.
        import urllib.parse
        import urllib.request
        owner,name=repository.split("/")
        url=(f"https://codeload.github.com/"
             f"{urllib.parse.quote(owner,safe='')}/"
             f"{urllib.parse.quote(name,safe='')}/tar.gz/{revision}")
        req=urllib.request.Request(
            url,headers={"User-Agent":"dashi-lean-world-source-builder/1"})
        with urllib.request.urlopen(req,timeout=60) as response:
            builder.ingest_archive(
                response,repository,revision,
                max_file_bytes=max_blob_bytes,
                max_total_bytes=max_total_bytes,
                max_transfer_bytes=max_transfer_bytes)
    elapsed=time.perf_counter()-start
    _,peak=tracemalloc.get_traced_memory()
    tracemalloc.stop()
    for original in builder.manifest():
        print(json.dumps(original,sort_keys=True))
    for record in processing:
        print(json.dumps(record,sort_keys=True))
    statuses={}
    for r in processing:
        name=r.get("status",r["kind"])
        statuses[name]=statuses.get(name,0)+1
    summary={
        "kind":"world-source-intake-summary", "repository":repository,
        "revision":revision, "transport":transport,
        "admitted_source_occurrences":builder.counters()["source_occurrences"],
        "skipped_sources":builder.skipped,
        "source_bytes":sum(r["size"] for r in builder.manifest()),
        "seconds":elapsed,"peak_python_bytes":peak,
        "source_complete":builder.skipped==0,
        "elaborated_declared_types":0,"kernel_checked_declarations":0,
        "compile_status_counts":statuses,
    }
    print(json.dumps(summary,sort_keys=True))
    return 0 if builder.skipped==0 and (
        compiler is None or not statuses.get("lean-elaboration-failed")) else 2


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("repository");p.add_argument("revision")
    p.add_argument("--transport",choices=["rest","archive"],default="archive")
    p.add_argument("--compile",action="store_true")
    p.add_argument("--flake",type=Path,default=Path("."))
    p.add_argument("--cache",type=Path)
    p.add_argument("--dependency-oleans",type=Path)
    p.add_argument("--closure-digest")
    p.add_argument("--max-blob-bytes",type=int,default=8*1024*1024)
    p.add_argument("--max-total-bytes",type=int,default=4*1024*1024*1024)
    p.add_argument("--max-transfer-bytes",type=int,default=2*1024*1024*1024)
    args=p.parse_args()
    if not REPO_RE.fullmatch(args.repository) or not COMMIT_RE.fullmatch(args.revision):
        p.error("immutable OWNER/REPO and 40-character Git commit revision required")
    compiler=None
    if args.compile:
        if not args.cache or not args.closure_digest:
            p.error("--compile requires --cache and --closure-digest")
        compiler=EphemeralLeanWorker(
            flake=args.flake,cache=args.cache,
            closure_digest=args.closure_digest,
            dependency_olean_dir=args.dependency_oleans)
    try:
        return ingest(
            args.repository,args.revision,transport=args.transport,
            compiler=compiler,max_blob_bytes=args.max_blob_bytes,
            max_total_bytes=args.max_total_bytes,
            max_transfer_bytes=args.max_transfer_bytes)
    except Exception as exc:
        # No success summary after partial failure: strict coverage accounting.
        print(f"LEAN_WORLD_INCOMPLETE: {type(exc).__name__}: {exc}",file=sys.stderr)
        return 2


if __name__=="__main__":
    raise SystemExit(main())
