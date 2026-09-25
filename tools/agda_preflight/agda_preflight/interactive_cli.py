from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
import statistics
import sys
import tempfile

from .source_index import SourceIndex
from .semantic_catalog import SemanticCatalog
from .timing import Profiler


def _run_diagnose(
    root: Path,
    index_path: Path,
    target: Path,
    semantic_catalog=None,
):
    profiler = Profiler()
    semantic = {}
    with profiler.stage("request.total"):
        with SourceIndex(root, index_path, profiler=profiler) as index:
            result = index.diagnose(target)
        if semantic_catalog is not None:
            with profiler.stage("semantic.catalog_lookup"):
                with SemanticCatalog(semantic_catalog) as catalog:
                    semantic = catalog.lookup(result.modules)
            profiler.count("semantic_snapshot_hits", len(semantic))
            profiler.count(
                "semantic_snapshot_misses",
                max(0, len(result.modules) - len(semantic)),
            )
    return result, profiler.snapshot(), semantic


def _percentile(values, fraction: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    rank = max(1, math.ceil(len(ordered) * fraction))
    return ordered[min(len(ordered), rank) - 1]


def _timing_summary(values) -> dict:
    ordered = list(values)
    return {
        "min_ms": round(min(ordered), 3) if ordered else 0.0,
        "p50_ms": round(statistics.median(ordered), 3) if ordered else 0.0,
        "p95_ms": round(_percentile(ordered, 0.95), 3),
        "max_ms": round(max(ordered), 3) if ordered else 0.0,
    }


def _format_diagnostic(diagnostic) -> str:
    head = (
        f"{diagnostic.path}:{diagnostic.line}:{diagnostic.column}: "
        f"{diagnostic.severity}: {diagnostic.code}: {diagnostic.message}"
    )
    details = (
        f" [evidence={diagnostic.evidence}; "
        f"requires={diagnostic.minimum_evidence}]"
    )
    if diagnostic.hint:
        return head + details + f"\n  hint: {diagnostic.hint}"
    return head + details


def _format_profile(snapshot) -> str:
    payload = snapshot.as_dict()
    counts = payload["counts"]
    stages = payload["stages_ms"]
    total = stages.get("request.total", 0.0)
    lines = [
        "dashi-agda profile:",
        f"  request.total: {total:.3f} ms",
        (
            "  closure: "
            f"{counts.get('modules_in_closure', 0)} modules; "
            f"parsed={counts.get('files_parsed', 0)}; "
            f"cached={counts.get('modules_cached', 0)}; "
            f"dirty={counts.get('dirty_modules', 0)}"
        ),
        (
            "  diagnostics: "
            f"cached={counts.get('diagnostics_cached', 0)}; "
            f"recomputed={counts.get('diagnostics_recomputed', 0)}"
        ),
    ]
    for name, milliseconds in sorted(stages.items()):
        if name == "request.total":
            continue
        lines.append(f"  {name}: {milliseconds:.3f} ms")
    return "\n".join(lines)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        prog="dashi-agda",
        description=(
            "Incremental source diagnostics for Agda. "
            "The diagnose path never invokes Agda."
        ),
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    diagnose = subparsers.add_parser(
        "diagnose",
        help="diagnose one module and its indexed dependency closure",
    )
    diagnose.add_argument("target", type=Path)
    diagnose.add_argument(
        "--root",
        type=Path,
        default=Path.cwd(),
        help="repository root (default: current directory)",
    )
    diagnose.add_argument(
        "--index",
        type=Path,
        default=Path(".cache/agda_preflight/source-index.sqlite3"),
        help="persistent source-index database",
    )
    diagnose.add_argument(
        "--semantic-catalog",
        type=Path,
        help=(
            "optional read-only agda2lean SQLite catalog; semantic hits are "
            "reported with freshness=unknown until checked source hashes are stored"
        ),
    )
    diagnose.add_argument(
        "--json",
        action="store_true",
        help="emit machine-readable diagnostics and profile data",
    )
    diagnose.add_argument(
        "--profile",
        action="store_true",
        help="print per-stage timing and cache counters",
    )
    diagnose.add_argument(
        "--errors-only",
        action="store_true",
        help="suppress warning/deferred diagnostics",
    )

    benchmark = subparsers.add_parser(
        "benchmark",
        help="measure cold bootstrap and repeated warm diagnose requests",
    )
    benchmark.add_argument("target", type=Path)
    benchmark.add_argument(
        "--root",
        type=Path,
        default=Path.cwd(),
        help="repository root (default: current directory)",
    )
    benchmark.add_argument(
        "--index",
        type=Path,
        default=Path(".cache/agda_preflight/source-index.sqlite3"),
        help="persistent source-index database used for warm runs",
    )
    benchmark.add_argument(
        "--runs",
        type=int,
        default=5,
        help="number of warm requests to measure (default: 5)",
    )
    benchmark.add_argument(
        "--json",
        action="store_true",
        help="emit benchmark results as JSON",
    )

    args = parser.parse_args(argv)

    if args.command == "diagnose":
        result, snapshot, semantic = _run_diagnose(
            args.root,
            args.index,
            args.target,
            args.semantic_catalog,
        )

        diagnostics = result.diagnostics
        if args.errors_only:
            diagnostics = [
                diagnostic
                for diagnostic in diagnostics
                if diagnostic.severity == "error"
            ]

        if args.json:
            payload = result.as_dict()
            payload["diagnostics"] = [
                diagnostic.as_dict() for diagnostic in diagnostics
            ]
            payload["profile"] = snapshot.as_dict()
            print(json.dumps(payload, indent=2, sort_keys=True))
        else:
            for diagnostic in diagnostics:
                print(_format_diagnostic(diagnostic))
            if not diagnostics:
                print("dashi-agda: no structural issues found")
            if args.profile:
                print(_format_profile(snapshot), file=sys.stderr)

        return 1 if any(d.severity == "error" for d in diagnostics) else 0

    if args.command == "benchmark":
        if args.runs < 1:
            parser.error("--runs must be at least 1")

        root = args.root.resolve()
        target = args.target if args.target.is_absolute() else root / args.target

        with tempfile.TemporaryDirectory(prefix="dashi-agda-bench-") as tmp:
            cold_index = Path(tmp) / "source-index.sqlite3"
            _, cold_snapshot = _run_diagnose(root, cold_index, target)

        # Prime the persistent warm index once. This prime is deliberately
        # excluded from the warm distribution.
        _run_diagnose(root, args.index, target)

        warm_snapshots = []
        for _ in range(args.runs):
            _, snapshot = _run_diagnose(root, args.index, target)
            warm_snapshots.append(snapshot)

        cold_payload = cold_snapshot.as_dict()
        warm_ms = [
            snapshot.as_dict()["stages_ms"].get("request.total", 0.0)
            for snapshot in warm_snapshots
        ]
        warm_parse_counts = [
            snapshot.counts.get("files_parsed", 0)
            for snapshot in warm_snapshots
        ]
        payload = {
            "target": str(target),
            "cold": cold_payload,
            "warm": {
                "runs": args.runs,
                "request_total": _timing_summary(warm_ms),
                "files_parsed": {
                    "min": min(warm_parse_counts),
                    "max": max(warm_parse_counts),
                },
                "all_zero_parse": all(value == 0 for value in warm_parse_counts),
            },
        }

        if args.json:
            print(json.dumps(payload, indent=2, sort_keys=True))
        else:
            cold_ms = cold_payload["stages_ms"].get("request.total", 0.0)
            warm = payload["warm"]["request_total"]
            print(f"target: {target}")
            print(f"cold: {cold_ms:.3f} ms")
            print(
                "warm: "
                f"min={warm['min_ms']:.3f} ms "
                f"p50={warm['p50_ms']:.3f} ms "
                f"p95={warm['p95_ms']:.3f} ms "
                f"max={warm['max_ms']:.3f} ms"
            )
            print(
                "warm files_parsed: "
                f"min={payload['warm']['files_parsed']['min']} "
                f"max={payload['warm']['files_parsed']['max']}"
            )

        return 0

    parser.error(f"unknown command: {args.command}")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
