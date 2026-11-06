#!/usr/bin/env python3
"""Fail-closed Agda 2.9 reserved BooleanFormula constructor migration check.

Search the whole complexity source tree, not just PR-changed files: the Cook
constructor is consumed by P!=NP and Karp21 downstream owners. Do not rename
Agda's legitimate 'variable' binding declarations or unrelated identifier
names. This is a source preflight, NOT an Agda compiler receipt.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re

LEGACY_QUALIFIED = re.compile(r"\b(?:Cook|SAT)\.variable\b")
LEGACY_CONSTRUCTOR = re.compile(r"^\s*variable\s*:", re.MULTILINE)
OWNERS = {
    "CookLevinCircuitGCTBoundary.agda",
    "BooleanFormulaSATSelfReductionExact.agda",
}


def check(root: Path) -> list[str]:
    failures: list[str] = []
    for path in sorted((root / "DASHI/Mathematics/Complexity").glob("*.agda")):
        source = path.read_text(encoding="utf-8")
        for lineno, line in enumerate(source.splitlines(), 1):
            if line.lstrip().startswith("--"):
                continue
            if LEGACY_QUALIFIED.search(line):
                failures.append(f"{path.relative_to(root)}:{lineno}: reserved qualified constructor")
            if path.name in OWNERS and LEGACY_CONSTRUCTOR.match(line):
                failures.append(f"{path.relative_to(root)}:{lineno}: reserved constructor declaration")
    return failures


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path,
                        default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    missing = check(args.repo_root.resolve())
    for finding in missing:
        print("FAIL:", finding)
    if missing:
        print(f"FAIL: {len(missing)} deprecated constructor references")
        return 1
    print("PASS: no Cook.variable/SAT.variable references or reserved constructor declarations")
    print("WARNING: lexical source preflight only; run the Agda 2.9 kernel independently")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
