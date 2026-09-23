from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

from .checker import Checker


def _format(diag) -> str:
    head = f"{diag.path}:{diag.line}:{diag.column}: {diag.code}: {diag.message}"
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
    args = parser.parse_args(argv)

    checker = Checker(args.root)

    if args.plan:
        for module in checker.affected_modules(args.file):
            print(module)
        return 0

    diagnostics = (
        checker.check_closure(args.file) if args.closure else checker.check(args.file)
    )

    if args.json:
        print(json.dumps([d.as_dict() for d in diagnostics], indent=2))
    else:
        for diag in diagnostics:
            print(_format(diag))
        if not diagnostics:
            print("agda-preflight: no high-confidence issues found")

    return 1 if diagnostics else 0


if __name__ == "__main__":
    raise SystemExit(main())
