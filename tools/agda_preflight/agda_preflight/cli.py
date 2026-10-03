from __future__ import annotations

import argparse
import json
import shlex
from pathlib import Path
import sys

from .checker import Checker, Diagnostic
from .rules import api_snapshot, api_drift
from .scope_backend import AgdaAutoRefineBackend, AgdaScopeCheckBackend, AgdaTypecheckBackend, ExternalScopeBackend
from .triage_delta import render_delta, triage_snapshot
from .triage_render import (
    build_triage,
    render_compact,
    render_grouped,
    render_location,
    render_verbose,
)


def _format(diag) -> str:
    head = (
        f"{diag.path}:{diag.line}:{diag.column}: {diag.severity}: "
        f"{diag.code}: {diag.message} "
        f"[evidence={diag.evidence}; requires={diag.minimum_evidence}]"
    )
    return head + (f"\n  hint: {diag.hint}" if diag.hint else "")


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        prog="dashi-agda-preflight",
        description="Fast tree-sitter + shallow semantic checks for DASHI Agda.",
    )
    parser.add_argument("file", type=Path)
    parser.add_argument(
        "--root",
        type=Path,
        default=Path.cwd(),
        help="repository root (default: current directory)",
    )
    parser.add_argument(
        "--closure",
        action="store_true",
        help="also check reverse-import consumers of FILE",
    )
    parser.add_argument(
        "--plan",
        action="store_true",
        help="print affected modules in frontier order and exit",
    )
    parser.add_argument("--json", action="store_true", help="emit lossless JSON diagnostics")
    parser.add_argument(
        "--errors-only",
        action="store_true",
        help="show only error diagnostics; exit status still reflects the full check",
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="hide warnings and success chatter; errors are still printed",
    )
    presentation = parser.add_mutually_exclusive_group()
    presentation.add_argument(
        "--compact",
        action="store_true",
        help="one logical diagnostic per line plus root-cause summary",
    )
    presentation.add_argument(
        "--verbose",
        action="store_true",
        help="show every raw diagnostic with full evidence metadata",
    )
    presentation.add_argument(
        "--by-location",
        action="store_true",
        help="show merged logical diagnostics in source order",
    )
    presentation.add_argument(
        "--by-cause",
        action="store_true",
        help="group human output by root cause (the default)",
    )
    parser.add_argument(
        "--absolute-paths",
        action="store_true",
        help="show absolute paths in human output instead of repository-relative paths",
    )
    parser.add_argument(
        "--only-kind",
        choices=(
            "receiver",
            "arity",
            "placeholder",
            "type-value",
            "parser",
            "shadowing",
            "rewrite",
            "deprecated-api",
            "agda-error",
            "agda-warning",
            "diagnostic",
        ),
        help="restrict human output to one actionability class; does not change exit status",
    )
    parser.add_argument(
        "--write-triage-summary",
        type=Path,
        help="write a stable root-cause/fingerprint snapshot for a later delta",
    )
    parser.add_argument(
        "--compare-triage-summary",
        type=Path,
        help="append a root-cause delta against a prior triage snapshot",
    )
    parser.add_argument("--write-api-snapshot", type=Path, help="write repository API summary JSON and exit")
    parser.add_argument("--api-baseline", type=Path, help="compare current exported API to a prior snapshot")
    parser.add_argument("--cycles", action="store_true", help="report repository import cycles containing FILE")
    scope_group = parser.add_mutually_exclusive_group()
    scope_group.add_argument(
        "--agda-scope-command",
        help=(
            "optional Agda-aware scope/elaboration command; receives FILE and "
            "returns confirmed/suppressed TSAGDA locations as JSON"
        ),
    )
    parser.add_argument(
        "--agda-scope-runner",
        help=(
            "exit-code-only scope checker command for --agda-auto-refine; "
            "supports the literal placeholder {file}"
        ),
    )
    parser.add_argument(
        "--agda-typecheck-runner",
        help=(
            "exit-code-only full Agda checker command for "
            "--agda-auto-refine=typecheck; supports {file}"
        ),
    )
    scope_group.add_argument(
        "--agda-scope-check",
        action="store_true",
        help="run Agda --only-scope-checking to suppress false scope diagnostics",
    )
    scope_group.add_argument(
        "--agda-typecheck-oracle",
        action="store_true",
        help="run full Agda checking to suppress false scope/type diagnostics",
    )
    scope_group.add_argument(
        "--agda-auto-refine",
        nargs="?",
        const="scope",
        choices=("scope", "typecheck"),
        help=(
            "refine only modules that actually need stronger evidence; "
            "optional value 'typecheck' also escalates typechecker-level findings"
        ),
    )
    parser.add_argument(
        "--agda-bin",
        default="agda",
        help="Agda executable for --agda-scope-check (default: agda)",
    )
    parser.add_argument(
        "--agda-extra-args",
        default="",
        help="extra arguments passed to Agda scope/typecheck refinement subprocesses",
    )
    args = parser.parse_args(argv)

    if args.agda_scope_runner and not args.agda_auto_refine:
        parser.error("--agda-scope-runner requires --agda-auto-refine")

    if args.agda_typecheck_runner and args.agda_auto_refine != "typecheck":
        parser.error(
            "--agda-typecheck-runner requires --agda-auto-refine=typecheck"
        )

    if args.json and args.compare_triage_summary:
        parser.error("--compare-triage-summary is a human-output option and cannot be combined with --json")

    agda_extra_args = tuple(shlex.split(args.agda_extra_args or ""))
    scope_backend = None
    if args.agda_scope_command:
        scope_backend = ExternalScopeBackend(args.agda_scope_command, cwd=args.root)
    elif args.agda_scope_check:
        scope_backend = AgdaScopeCheckBackend(
            args.agda_bin,
            cwd=args.root,
            extra_args=agda_extra_args,
        )
    elif args.agda_typecheck_oracle:
        scope_backend = AgdaTypecheckBackend(
            args.agda_bin,
            cwd=args.root,
            extra_args=agda_extra_args,
        )
    elif args.agda_auto_refine:
        scope_backend = AgdaAutoRefineBackend(
            args.agda_bin,
            cwd=args.root,
            typecheck=args.agda_auto_refine == "typecheck",
            extra_args=agda_extra_args,
            scope_command=args.agda_scope_runner,
            typecheck_command=args.agda_typecheck_runner,
        )
    checker = Checker(args.root, scope_backend=scope_backend)

    if args.write_api_snapshot:
        args.write_api_snapshot.write_text(
            json.dumps(api_snapshot(checker), indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        if not args.quiet:
            print(args.write_api_snapshot)
        return 0

    if args.cycles:
        graph = checker.dependency_graph()
        start = checker.parse_summary(args.file).module_name
        state = {}
        stack = []
        cycles = []

        def visit(node):
            state[node] = 1
            stack.append(node)
            for dep in graph.get(node, ()):
                if dep not in graph:
                    continue
                if state.get(dep, 0) == 0:
                    visit(dep)
                elif state.get(dep) == 1 and dep in stack:
                    cycle = stack[stack.index(dep):] + [dep]
                    if cycle not in cycles:
                        cycles.append(cycle)
            stack.pop()
            state[node] = 2

        visit(start)
        for cycle in cycles:
            print(" -> ".join(cycle))
        return 1 if cycles else 0

    if args.plan:
        for module in checker.affected_modules(args.file):
            print(module)
        return 0

    diagnostics = (
        checker.check_closure(args.file) if args.closure else checker.check(args.file)
    )
    if args.api_baseline:
        baseline = json.loads(args.api_baseline.read_text(encoding="utf-8"))
        diagnostics.extend(api_drift(checker, baseline, Diagnostic))

    errors_only = args.errors_only or args.quiet
    displayed = (
        [diag for diag in diagnostics if diag.severity == "error"]
        if errors_only
        else diagnostics
    )
    report = build_triage(
        displayed,
        args.root,
        absolute_paths=args.absolute_paths,
        only_kind=args.only_kind,
    )

    if args.write_triage_summary:
        args.write_triage_summary.parent.mkdir(parents=True, exist_ok=True)
        args.write_triage_summary.write_text(
            json.dumps(triage_snapshot(report), indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

    delta_text = None
    if args.compare_triage_summary:
        previous = json.loads(args.compare_triage_summary.read_text(encoding="utf-8"))
        delta_text = render_delta(previous, report)

    if not (args.quiet and not displayed):
        if args.json:
            # JSON remains deliberately lossless: no sibling merging or display
            # clustering. This keeps MCP/automation consumers stable.
            print(json.dumps([d.as_dict() for d in displayed], indent=2))
        elif displayed:
            if args.verbose:
                print(render_verbose(report))
            elif args.compact:
                print(render_compact(report))
            elif args.by_location:
                print(render_location(report))
            else:
                # --by-cause is an explicit spelling of the default.
                print(render_grouped(report))
            if delta_text:
                print()
                print(delta_text)
        else:
            if args.errors_only:
                print("agda-preflight: no errors found")
            else:
                print("agda-preflight: no high-confidence issues found")
            if delta_text:
                print(delta_text)

    return 1 if any(d.severity == "error" for d in diagnostics) else 0


if __name__ == "__main__":
    raise SystemExit(main())
