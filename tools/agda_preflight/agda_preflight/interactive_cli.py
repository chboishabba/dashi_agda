from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

from .source_index import SourceIndex
from .timing import Profiler


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

    args = parser.parse_args(argv)

    if args.command == "diagnose":
        profiler = Profiler()
        with profiler.stage("request.total"):
            with SourceIndex(
                args.root,
                args.index,
                profiler=profiler,
            ) as index:
                result = index.diagnose(args.target)

        diagnostics = result.diagnostics
        if args.errors_only:
            diagnostics = [
                diagnostic
                for diagnostic in diagnostics
                if diagnostic.severity == "error"
            ]

        snapshot = profiler.snapshot()
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

    parser.error(f"unknown command: {args.command}")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
