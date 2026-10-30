#!/usr/bin/env python3
"""Static Agda source hygiene regression, NOT a typechecker.

Used after an earlier CT11 file accidentally included literal '\\n'
between import statements. Checks duplicate exact import declarations,
embedded escaped linebreaks, explicit holes, postulates/termination
escapes. The --require-safe option separately gates modules missing
a safe pragma; default audit reports them without claiming a safe proof.

Mathematical proof ownership remains in the imported Agda modules;
this checker certifies only text-level source integrity.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys

IMPORT = re.compile(r"^\s*(?:open\s+)?import\s+([^\s]+)", re.M)
BAD_POSTULATE = re.compile(r"^\s*postulate\b", re.M)
HOLE = re.compile(r"(?<!\S)\?(?!\S)|=\s*\{!|\{!.*?!\}", re.S)
TERMINATION = re.compile(r"\{\-#\s*(?:TERMINATING|NON_TERMINATING)\s*#\-\}")

def check_source(path: Path, require_safe: bool = False) -> list[str]:
    raw = path.read_text(encoding="utf-8")
    problems = []
    for lineno, line in enumerate(raw.splitlines(), 1):
        if line.lstrip().startswith(("import ", "open import ")) and "\\n" in line:
            problems.append(f"line {lineno}: literal escaped newline in import")
    imports = IMPORT.findall(raw)
    repeats = sorted(set(x for x in imports if imports.count(x) > 1))
    problems += [f"duplicate import: {x}" for x in repeats]
    if BAD_POSTULATE.search(raw):
        problems.append("postulate declaration")
    if TERMINATION.search(raw):
        problems.append("termination pragma")
    if HOLE.search(raw):
        problems.append("explicit unresolved hole")
    if require_safe and "{-# OPTIONS --safe #-}" not in raw:
        problems.append("missing explicit --safe pragma")
    return problems

def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("paths", nargs="*", type=Path)
    parser.add_argument("--require-safe", action="store_true")
    args = parser.parse_args()
    paths = args.paths or sorted(set(Path("DASHI/Arithmetic").glob("TwinPrime*.agda"))
                                 | set(Path("DASHI/Arithmetic").glob("*Mangoldt*.agda")))
    if not paths:
        print("ERROR: no source paths matched")
        return 2
    failures = 0
    missing_safe = 0
    for path in paths:
        if not path.exists():
            print(f"{path}: MISSING")
            failures += 1
            continue
        raw = path.read_text(encoding="utf-8")
        if "{-# OPTIONS --safe #-}" not in raw:
            missing_safe += 1
        for problem in check_source(path, args.require_safe):
            print(f"{path}: {problem}")
            failures += 1
    print({"scanned_sources": len(paths), "static_failures": failures,
           "without_explicit_safe": missing_safe,
           "agda_kernel_checked": False})
    return 1 if failures else 0

if __name__ == "__main__":
    sys.exit(main())
