#!/usr/bin/env python3
"""Deterministic static consistency check for the 3+1 / YM / KK roadmap.

This audit verifies that exactly 176 lemma IDs in P00..P11 are present,
unique, consecutive by phase, in canonical checkbox order, and that phase
descriptions/exit clauses and source-branch warning remain explicit.

This checks a roadmap's internal structure ONLY. It proves no Agda theorem,
constructs no physical measure, and verifies no math/physics correctness.
"""
from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path
import re

ROADMAP = Path("Docs/roadmaps/Emergent31QuantumYMKKExactLemmaRoadmap20261103.md")
EXPECTED = (10, 12, 16, 14, 12, 16, 20, 14, 17, 13, 14, 18)
LEMMA_PATTERN = re.compile(r"^- \[ \] \*\*(P(\d\d)\.L(\d\d))\*\*", re.MULTILINE)
PHASE_PATTERN = re.compile(r"^## P(\d\d) — ", re.MULTILINE)

def check_roadmap(text: str) -> dict[str, int]:
    lemma_matches = list(LEMMA_PATTERN.finditer(text))
    all_ids = [m.group(1) for m in lemma_matches]
    assert len(all_ids) == 176, f"expected 176, got {len(all_ids)}"
    assert len(set(all_ids)) == len(all_ids), "duplicate lemma IDs"
    phases = [int(m.group(1)) for m in PHASE_PATTERN.finditer(text)]
    assert phases == list(range(12)), f"phases missing/out of order: {phases!r}"
    counts = Counter(int(m.group(2)) for m in lemma_matches)
    assert tuple(counts[p] for p in range(12)) == EXPECTED, f"incorrect per-phase counts: {counts}"
    expected_ids = [f"P{phase:02d}.L{num:02d}"
                    for phase, limit in enumerate(EXPECTED)
                    for num in range(1, limit + 1)]
    assert all_ids == expected_ids, "IDs are missing, nonconsecutive, or out of order"
    assert text.count("**Deliverable:**") >= 11, "phase deliverables not enumerated"
    assert text.count("**Exit:**") >= 11, "phase exit conditions not enumerated"
    assert "5bb34d44bac92dfe16544fcde07c65e37d875172" in text, "missing pinned #1444 source"
    assert "H_OS" in text and "H_clock" in text, "missing central clock/OS physical bridge"
    assert "R443" in text and "R445" in text and "R320" in text and "R333" in text, "missing Clay source"
    assert "Standalone Clay completion" in text, "missing Clay independence boundary"
    return {f"P{p:02d}": counts[p] for p in range(12)}

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--file", type=Path, default=ROADMAP)
    args = parser.parse_args()
    counts = check_roadmap(args.file.read_text(encoding="utf-8"))
    print("PASS: 12 ordered phases, 176 unique contiguous exact lemma IDs")
    print("PASS: phase deliverables/exits and same-clock/OS + Clay separation")
    print(" ".join(f"{phase}:{count}" for phase, count in counts.items()))
    print("NOTE: static audit only; no Agda kernel or physical proof was checked")

if __name__ == "__main__":
    main()
