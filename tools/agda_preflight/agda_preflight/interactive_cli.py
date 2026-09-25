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
from .apply_edits import apply_text_edits, EditApplicationError
from .timing import Profiler


def _run_diagnose(
    root: Path,
    index_path: Path,
    target: Path,
    semantic_catalog=None,
    jobs: int = 1,
):
    profiler = Profiler()
    semantic = {}
    with profiler.stage("request.total"):
        with SourceIndex(
            root,
            index_path,
            profiler=profiler,
            jobs=jobs,
        ) as index:
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


def _diagnostic_priority(diagnostic):
    return (
        0 if diagnostic.severity == "error" else 1,
        0 if diagnostic.evidence_sufficient else 1,
        0 if any(fix.edits for fix in diagnostic.fixes) else 1,
        str(diagnostic.path),
        diagnostic.line,
        diagnostic.column,
        diagnostic.code,
    )


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
        "--jobs",
        type=int,
        default=0,
        help="cold-bootstrap workers; 0 = auto, 1 = sequential (default: auto)",
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
        "--jobs",
        type=int,
        default=0,
        help="cold-bootstrap workers; 0 = auto (default: auto)",
    )
    benchmark.add_argument(
        "--json",
        action="store_true",
        help="emit benchmark results as JSON",
    )
    benchmark.add_argument(
        "--max-warm-ms",
        type=float,
        default=10000.0,
        help="maximum allowed warm p95 latency (default: 10000 ms)",
    )
    benchmark.add_argument(
        "--max-cold-ms",
        type=float,
        default=60000.0,
        help="maximum allowed cold bootstrap latency (default: 60000 ms)",
    )

    next_error = subparsers.add_parser(
        "next-error",
        help="return the highest-priority current diagnostic for an agent",
    )
    next_error.add_argument("target", type=Path)
    next_error.add_argument(
        "--root",
        type=Path,
        default=Path.cwd(),
        help="repository root (default: current directory)",
    )
    next_error.add_argument(
        "--index",
        type=Path,
        default=Path(".cache/agda_preflight/source-index.sqlite3"),
        help="persistent source-index database",
    )
    next_error.add_argument(
        "--jobs",
        type=int,
        default=0,
        help="cold-bootstrap workers; 0 = auto (default: auto)",
    )
    next_error.add_argument(
        "--require-fix",
        action="store_true",
        help="only return diagnostics that have at least one suggested fix",
    )
    next_error.add_argument(
        "--json",
        action="store_true",
        help="emit machine-readable result",
    )

    apply_fix = subparsers.add_parser(
        "apply-fix",
        help="apply an exact suggested edit by diagnostic ID",
    )
    apply_fix.add_argument("target", type=Path)
    apply_fix.add_argument("diagnostic_id")
    apply_fix.add_argument(
        "--fix",
        type=int,
        default=0,
        help="fix index on the diagnostic (default: 0)",
    )
    apply_fix.add_argument(
        "--root",
        type=Path,
        default=Path.cwd(),
        help="repository root (default: current directory)",
    )
    apply_fix.add_argument(
        "--index",
        type=Path,
        default=Path(".cache/agda_preflight/source-index.sqlite3"),
        help="persistent source-index database",
    )
    apply_fix.add_argument(
        "--jobs",
        type=int,
        default=0,
        help="cold-bootstrap workers; 0 = auto (default: auto)",
    )
    apply_fix.add_argument(
        "--allow-likely",
        action="store_true",
        help="allow edits classified as likely; speculative fixes are never applied",
    )
    apply_fix.add_argument(
        "--json",
        action="store_true",
        help="emit machine-readable application/recheck result",
    )

    args = parser.parse_args(argv)

    if args.command == "diagnose":
        result, snapshot, semantic = _run_diagnose(
            args.root,
            args.index,
            args.target,
            args.semantic_catalog,
            args.jobs,
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
            payload["semantic"] = {
                module: item.as_dict()
                for module, item in sorted(semantic.items())
            }
            print(json.dumps(payload, indent=2, sort_keys=True))
        else:
            for diagnostic in diagnostics:
                print(_format_diagnostic(diagnostic))
            if not diagnostics:
                print("dashi-agda: no structural issues found")
            if args.semantic_catalog is not None:
                print(
                    "semantic snapshots: "
                    f"{len(semantic)}/{len(result.modules)} "
                    "(freshness unknown)",
                    file=sys.stderr,
                )
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
            _, cold_snapshot, _ = _run_diagnose(
                root, cold_index, target, jobs=args.jobs
            )

        # Prime the persistent warm index once. This prime is deliberately
        # excluded from the warm distribution.
        _run_diagnose(root, args.index, target, jobs=args.jobs)

        warm_snapshots = []
        for _ in range(args.runs):
            _, snapshot, _ = _run_diagnose(
                root, args.index, target, jobs=args.jobs
            )
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
        warm_summary = _timing_summary(warm_ms)
        cold_ms = cold_payload["stages_ms"].get("request.total", 0.0)
        all_zero_parse = all(value == 0 for value in warm_parse_counts)
        slo_passed = (
            cold_ms <= args.max_cold_ms
            and warm_summary["p95_ms"] <= args.max_warm_ms
            and all_zero_parse
        )
        payload = {
            "target": str(target),
            "cold": cold_payload,
            "warm": {
                "runs": args.runs,
                "request_total": warm_summary,
                "files_parsed": {
                    "min": min(warm_parse_counts),
                    "max": max(warm_parse_counts),
                },
                "all_zero_parse": all_zero_parse,
            },
            "slo": {
                "max_cold_ms": args.max_cold_ms,
                "max_warm_ms": args.max_warm_ms,
                "passed": slo_passed,
            },
        }

        if args.json:
            print(json.dumps(payload, indent=2, sort_keys=True))
        else:
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

        print(
            "SLO: " + ("PASS" if slo_passed else "FAIL")
        ) if not args.json else None
        return 0 if slo_passed else 1

    if args.command == "next-error":
        result, snapshot, _ = _run_diagnose(
            args.root,
            args.index,
            args.target,
            jobs=args.jobs,
        )
        candidates = list(result.diagnostics)
        if args.require_fix:
            candidates = [
                item for item in candidates
                if item.fixes
            ]
        candidates.sort(key=_diagnostic_priority)
        diagnostic = candidates[0] if candidates else None

        if args.json:
            print(
                json.dumps(
                    {
                        "status": "diagnostic" if diagnostic is not None else "clean",
                        "diagnostic": (
                            diagnostic.as_dict()
                            if diagnostic is not None
                            else None
                        ),
                        "profile": snapshot.as_dict(),
                    },
                    indent=2,
                    sort_keys=True,
                )
            )
        elif diagnostic is None:
            print("dashi-agda: no matching diagnostics")
        else:
            print(_format_diagnostic(diagnostic))
            for index, fix in enumerate(diagnostic.fixes):
                print(
                    f"  fix[{index}] {fix.applicability}: {fix.title} "
                    f"[validate={fix.validation}]"
                )

        return 0

    if args.command == "apply-fix":
        result, before_profile, _ = _run_diagnose(
            args.root,
            args.index,
            args.target,
            jobs=args.jobs,
        )
        diagnostic = next(
            (
                item for item in result.diagnostics
                if item.diagnostic_id == args.diagnostic_id
            ),
            None,
        )
        if diagnostic is None:
            parser.error(
                "diagnostic ID is not present in the current source-index result"
            )
        if args.fix < 0 or args.fix >= len(diagnostic.fixes):
            parser.error(
                f"diagnostic has {len(diagnostic.fixes)} fix(es); "
                f"--fix {args.fix} is out of range"
            )

        fix = diagnostic.fixes[args.fix]
        if fix.applicability == "speculative":
            parser.error("speculative fixes cannot be machine-applied")
        if fix.applicability == "likely" and not args.allow_likely:
            parser.error(
                "likely fixes require --allow-likely"
            )
        if not fix.edits:
            parser.error("selected fix has no exact machine-applicable edits")

        try:
            changed = apply_text_edits(fix.edits)
        except EditApplicationError as error:
            parser.error(str(error))

        after, after_profile, _ = _run_diagnose(
            args.root,
            args.index,
            args.target,
            jobs=args.jobs,
        )
        resolved = all(
            item.diagnostic_id != args.diagnostic_id
            for item in after.diagnostics
        )
        payload = {
            "diagnostic_id": args.diagnostic_id,
            "fix": fix.as_dict(),
            "changed_files": [str(path) for path in changed],
            "resolved": resolved,
            "before_profile": before_profile.as_dict(),
            "after_profile": after_profile.as_dict(),
        }

        if args.json:
            print(json.dumps(payload, indent=2, sort_keys=True))
        else:
            print(f"applied: {fix.title}")
            for path in changed:
                print(f"  changed: {path}")
            print(
                "recheck: "
                + ("diagnostic resolved" if resolved else "diagnostic remains")
            )

        return 0 if resolved else 1

    parser.error(f"unknown command: {args.command}")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
