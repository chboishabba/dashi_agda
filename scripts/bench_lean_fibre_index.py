#!/usr/bin/env python3
"""Synthetic benchmark for PR #1483 (no network, no CI dependency).

Run from a worktree containing scripts/lean_world_fibre_index.py:
  python3 scripts/bench_lean_fibre_index.py --counts 1000 10000 50000
Measurements exclude Git download, Lean elaboration, PostgreSQL and checking.
"""
from __future__ import annotations
import argparse
import gc
import json
import statistics
import time
import tracemalloc

def benchmark(counts: list[int], budget: int, queries: int, sharing: int):
    from lean_world_fibre_index import Declaration, SourceOccurrence, FibreIndex
    reports = []
    for count in counts:
        gc.collect()
        tracemalloc.start()
        world = FibreIndex()
        started = time.perf_counter()
        for i in range(count):
            origin = SourceOccurrence(
                f"r{i // 500:06d}", "a" * 40, f"D{i:09d}", f"proof-{i}", "author")
            dtype = f"type-{i // sharing:012d}".encode("ascii")
            world.admit(Declaration(origin, "lean4", "Eq", "0", dtype))
        ingest_s = time.perf_counter() - started
        _current, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        elapsed = []
        for _ in range(queries):
            start = time.perf_counter()
            result = world.candidates("lean4", "Eq", "0", budget)
            elapsed.append(time.perf_counter() - start)
        assert len(result.matches) == min(budget, count)
        assert result.remaining == max(0, count - budget)
        reports.append({
            "declarations": count, "ingest_seconds": round(ingest_s, 3),
            "ingest_per_second": round(count / ingest_s),
            "peak_traced_mib": round(peak / 1048576, 2),
            "lookup_p50_ms": round(statistics.median(elapsed) * 1000, 3),
            "lookup_max_ms": round(max(elapsed) * 1000, 3),
            "returned": len(result.matches), "omitted": result.remaining,
            "exact_statements": world.exact_statement_count(),
        })
        del world
    return reports

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--counts", nargs="+", type=int, default=[1000, 10000, 50000])
    p.add_argument("--budget", type=int, default=20)
    p.add_argument("--queries", type=int, default=7)
    p.add_argument("--sharing", type=int, default=4)
    args = p.parse_args()
    if any(n < 1 for n in args.counts) or min(args.queries, args.sharing) < 1 or args.budget < 0:
        p.error("counts/queries/sharing must be positive, budget nonnegative")
    print(json.dumps({
        "benchmark": "synthetic in-memory only",
        "source": "PR 1483 FibreIndex (requires module in same worktree)",
        "results": benchmark(args.counts, args.budget, args.queries, args.sharing),
    }, indent=2))

if __name__ == "__main__":
    main()
