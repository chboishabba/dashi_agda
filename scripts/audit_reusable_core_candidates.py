#!/usr/bin/env python3
"""Audit reusable receipt-core migration candidates.

The report is intentionally textual and conservative.  It identifies exact
local listCount duplicates plus semantic patterns that should be migrated by
hand through adapter fields rather than rewritten blindly.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
AGDA_ROOT = ROOT / "DASHI"

LIST_COUNT_RE = re.compile(
    r"(?ms)^listCount\s*:\s*.*?\n"
    r"listCount\s+\[\]\s*=\s*(?:zero|0)\s*\n"
    r"listCount\s+\(_\s*∷\s*xs\)\s*=\s*suc\s*\(listCount\s+xs\)"
)


@dataclass(frozen=True)
class Pattern:
    label: str
    needle: str


PATTERNS = (
    Pattern("count proofs", "CountIs"),
    Pattern("fail-closed authority bits", "Authority"),
    Pattern("carrier non-promotion bits", "PromotedHereIsFalse"),
    Pattern("PNF package rows", "SelectorPackage"),
    Pattern("spectral/Hodge diagnostics", "Hodge"),
)


def agda_files() -> list[Path]:
    return sorted(AGDA_ROOT.rglob("*.agda"))


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def main() -> int:
    list_count_hits: list[Path] = []
    semantic_hits: dict[str, list[Path]] = {pattern.label: [] for pattern in PATTERNS}

    for path in agda_files():
        text = path.read_text(encoding="utf-8")
        if LIST_COUNT_RE.search(text):
            list_count_hits.append(path)
        for pattern in PATTERNS:
            if pattern.needle in text:
                semantic_hits[pattern.label].append(path)

    print("Reusable core candidate audit")
    print("=============================")
    print()
    print(f"Exact local listCount duplicates: {len(list_count_hits)}")
    for path in list_count_hits:
        print(f"  - {rel(path)}")

    print()
    print("Semantic duplicate / adapter candidates:")
    for label, paths in semantic_hits.items():
        print(f"  {label}: {len(paths)}")
        for path in paths[:40]:
            print(f"    - {rel(path)}")
        if len(paths) > 40:
            print(f"    ... {len(paths) - 40} more deferred candidates")

    print()
    print(
        "Deferred by policy: broad historical receipt leaves, fragile GR/NS/YM "
        "analytic proofs, and non-exact count helpers."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
