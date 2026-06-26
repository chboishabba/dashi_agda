#!/usr/bin/env python3
"""Conservatively replace exact local listCount definitions with the core one."""

from __future__ import annotations

import argparse
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]

LIST_COUNT_RE = re.compile(
    r"(?ms)^listCount\s*:\s*.*?\n"
    r"listCount\s+\[\]\s*=\s*(?:zero|0)\s*\n"
    r"listCount\s+\(_\s*∷\s*xs\)\s*=\s*suc\s*\(listCount\s+xs\)\n*"
)


def add_import(text: str) -> str:
    import_line = "open import DASHI.Core.FiniteReceiptList using (listCount)\n"
    if import_line.strip() in text:
        return text
    matches = list(re.finditer(r"^(?:open import|import) .*$", text, re.MULTILINE))
    if not matches:
        raise ValueError("no import block found")
    insert_at = matches[-1].end()
    return text[:insert_at] + "\n" + import_line.rstrip("\n") + text[insert_at:]


def refactor(path: Path, check: bool) -> bool:
    text = path.read_text(encoding="utf-8")
    if not LIST_COUNT_RE.search(text):
        return False
    rewritten = LIST_COUNT_RE.sub("", text, count=1)
    rewritten = add_import(rewritten)
    if rewritten == text:
        return False
    if check:
        print(path.relative_to(ROOT).as_posix())
        return True
    path.write_text(rewritten, encoding="utf-8")
    print(f"updated {path.relative_to(ROOT).as_posix()}")
    return True


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("paths", nargs="+", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()

    changed = False
    for raw_path in args.paths:
        path = raw_path if raw_path.is_absolute() else ROOT / raw_path
        changed = refactor(path, args.check) or changed
    return 1 if args.check and changed else 0


if __name__ == "__main__":
    raise SystemExit(main())
