#!/usr/bin/env python3
"""Reproducible, pinned multi-repo Lean source-to-world throughput harness.

Input manifest (no invented moving HEAD refs):
{
 "repositories":[
   {"repository":"owner/small","revision":"<40 hex>","class":"small"},
   {"repository":"owner/medium","revision":"<40 hex>","class":"medium"},
   {"repository":"owner/large","revision":"<40 hex>","class":"large"}
 ]
}

Runs bench_lean_world_acquisition.py LIVE as a separate process per repository.
No CI dependency, no Docker, no clone; never declares Lean elaboration or
PostgreSQL production storage validated. Fail closed on ANY incomplete corpus.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
import time

REPO = re.compile(r"^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$")
REV = re.compile(r"^[0-9a-fA-F]{40}$")


def run_corpus(manifest: dict, *, minimum: int = 3, timeout: int = 3600):
    entries=manifest.get("repositories")
    if not isinstance(entries,list) or len(entries)<minimum:
        raise ValueError("at least three pinned representative repositories required")
    if len({r.get("class") for r in entries})<3:
        raise ValueError("require at least three distinct repository size/classes")
    if len({r.get("repository") for r in entries})!=len(entries):
        raise ValueError("duplicate repositories in benchmark manifest")
    results=[]
    bench=Path(__file__).resolve().parent/"bench_lean_world_acquisition.py"
    for item in entries:
        repo,rev=item.get("repository"),item.get("revision")
        if not isinstance(repo,str) or not REPO.fullmatch(repo) or (
            not isinstance(rev,str) or not REV.fullmatch(rev)):
            raise ValueError("every repository requires immutable owner/name + commit")
        cmd=[sys.executable,str(bench),"--mode","live",
             "--repo",repo,"--revision",rev]
        completed=subprocess.run(cmd,capture_output=True,text=True,
                                 timeout=timeout,check=False)
        if completed.returncode:
            raise RuntimeError(
                f"real source-to-world measurement INCOMPLETE for {repo}: "
                +completed.stderr[-1500:])
        rows=json.loads(completed.stdout)["runs"]
        if len(rows)!=1 or rows[0].get("mode")!="live-source-to-world-not-lean":
            raise RuntimeError("benchmark output is not a live intake")
        row=rows[0]
        a,b=row["archive"],row["selective_git_blobs"]
        if a["skipped"] or b["skipped"] or (
            a["source_occurrences"]!=b["source_occurrences"] or
            a["source_bytes"]!=b["source_bytes"]):
            raise RuntimeError("archive/REST coverage differs or is incomplete")
        results.append({"repository":repo,"revision":rev,"class":item["class"],
                        "source_files":a["source_occurrences"],
                        "archive":a,"selective_git_blobs":b})
    return {
        "benchmark":"live-pinned-repo-original-source-to-world",
        "complete":True,
        "not_measured":["Lean elaboration/kernel checks",
                        "PostgreSQL on-disk peak and DB query throughput",
                        "actual compiled dependency closure build time"],
        "results":results,
    }


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--manifest",type=Path,required=True)
    p.add_argument("--out",type=Path)
    p.add_argument("--timeout",type=int,default=3600)
    args=p.parse_args()
    try:
        manifest=json.loads(args.manifest.read_text(encoding="utf-8"))
        report=run_corpus(manifest,timeout=args.timeout)
        output=json.dumps(report,sort_keys=True,indent=2)+"\n"
        if args.out:
            args.out.write_text(output,encoding="utf-8")
        print(output,end="")
        return 0
    except (ValueError,KeyError,RuntimeError,subprocess.TimeoutExpired,OSError) as e:
        print(f"CORPUS_BENCHMARK_INCOMPLETE: {e}",file=sys.stderr)
        return 2


if __name__=="__main__":
    raise SystemExit(main())
