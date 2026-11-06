#!/usr/bin/env python3
"""Fail-closed #1460 phases vs original 186 exact Agda-lemma ledger.

STATUS: source/document consistency only. This does NOT run Agda, verify
same-state quantum/KK physical meaning, or establish Yang--Mills.
"""
from collections import Counter
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
PHASES = ROOT / "Docs/roadmaps/TSFVUnificationExecutionPhasesDeliverablesExactLemmas20261106.md"
ROADMAP = ROOT / "Docs/roadmaps/Emergent31QuantumYMKKExactLemmaRoadmap20261103.md"
PHASE_PATTERN = re.compile(
    r"^\| `([VOHKB]\d{2})` \| `([^\x60]+)` \| ([^|]+) \| ([^|]+) \| ([^|]+) \|$",
    re.MULTILINE,
)
CANONICAL = re.compile(r"^- \[[ x]\] \*\*(P\d{2}\.L\d{2})\*\* ", re.MULTILINE)
STATUS_ROW = re.compile(r"^\| `(P\d{2}\.L\d{2})` \| ", re.MULTILINE)
COMPONENT = re.compile(r"(?:(P\d{2})\.)?L(\d{2})(?:–L(\d{2}))?\Z")
EXPECTED_GROUP_COUNTS = {"V": 7, "O": 12, "H": 12, "K": 9, "B": 8}


def expand_ids(spec):
    previous = None
    expanded = []
    for token in spec.split(","):
        match = COMPONENT.fullmatch(token.strip())
        assert match, f"invalid canonical lemma reference {token!r}"
        group, lo, hi = match.groups()
        group = group or previous
        assert group, f"unscoped reference in {spec}"
        previous = group
        start, stop = int(lo), int(hi or lo)
        assert stop >= start, f"descending range in {spec}"
        expanded.extend(f"{group}.L{i:02d}" for i in range(start, stop + 1))
    return expanded


def main():
    roadmap = ROADMAP.read_text(encoding="utf-8")
    phase_source = PHASES.read_text(encoding="utf-8")
    ids = CANONICAL.findall(roadmap)
    status = STATUS_ROW.findall(roadmap)
    assert len(ids) == len(set(ids)) == 186
    assert len(status) == len(set(status)) == 186
    assert set(ids) == set(status), "canonical 186 vs status mismatch"

    rows = PHASE_PATTERN.findall(phase_source)
    phase_ids = [row[0] for row in rows]
    assert len(rows) == len(set(phase_ids)) == 48, (
        f"expected 48 unique execution tasks, saw {len(rows)}"
    )
    assert dict(Counter(x[0] for x in phase_ids)) == EXPECTED_GROUP_COUNTS

    referenced = set()
    for task, spec, goal, leaf, state in rows:
        assert goal.strip() and leaf.strip() and state.strip(), task
        for lemma in expand_ids(spec):
            assert lemma in ids, f"{task}: missing original lemma {lemma}"
            referenced.add(lemma)
        assert "OPEN" in state or "PINNED" in state or "OPTIONAL" in state or "SOURCE" in state, (
            f"{task}: status needs explicit scope and proof receipt"
        )
    assert "YMClayPhysicalCubeDobrushinFromGibbsExact" in phase_source
    assert "S01" in phase_source and "S11" in phase_source
    assert "TSFVAcousticMassInverseBidiNoGoExact" in phase_source
    assert "TSFVAcousticLocalImpulseThirdDerivativeExact" in phase_source
    print(f"PASS 186 unique canonical lemmas and 186 status rows")
    print(f"PASS 48 unique tasks / five phases / {len(referenced)} distinct canonical IDs covered")
    print("SOURCE phase coverage only; no Agda kernel/physical E1 or YM promotion")


if __name__ == "__main__":
    main()
