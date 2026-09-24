from __future__ import annotations

import argparse
import json
import shlex
from pathlib import Path
import sys

from .checker import Checker, Diagnostic
from .rules import api_snapshot, api_drift
from .scope_backend import AgdaAutoRefineBackend, AgdaScopeCheckBackend, AgdaTypecheckBackend, ExternalScopeBackend


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
    parser.add_argument("--json", action="store_true", help="emit JSON diagnostics")
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
        )
    checker = Checker(args.root, scope_backend=scope_backend)

    if args.write_api_snapshot:
        args.write_api_snapshot.write_text(
            json.dumps(api_snapshot(checker), indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
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

    if args.json:
        print(json.dumps([d.as_dict() for d in diagnostics], indent=2))
    else:
        for diag in diagnostics:
            print(_format(diag))
        if not diagnostics:
            print("agda-preflight: no high-confidence issues found")

    return 1 if any(d.severity == "error" for d in diagnostics) else 0


if __name__ == "__main__":
    raise SystemExit(main())
