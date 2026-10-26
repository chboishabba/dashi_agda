#!/usr/bin/env python3
"""Fail-closed original 20-space acceptance matrix validator.

The original question concerns TWENTY distinct source-selected
topological objects, not merely the seven highest-fanout Pareto leaves.
This parser preserves each object, its concrete evidence and its still
open *same-object* acceptance condition. It does not perform
mathematical proof checking or infer that a historical source
statement has been established on a DASHI representation.

Original sources/implementations retain their actual attribution in:
  Docs/topology/ExoticTwentyOriginalInquiryPhaseDeliverables20261027.md
  DASHI/Mathematics/Topology/ExoticSourceGenealogyParetoExact.agda

If a row is promoted to "closed", a future updater MUST add a
separate exact pinned kernel/paper theorem receipt and update this
validator deliberately. A passing checklist is never a theorem.
"""
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parent.parent
LEDGER = ROOT / "Docs/topology/ExoticTwentyOriginalInquiryPhaseDeliverables20261027.md"

EXPECTED_OBJECTS = (
    "Lakes of Wada", "Wild knot", "Wild arc", "Fox–Artin wild arc",
    "Cantor-tree surface", "Jacob’s ladder", "Loch Ness monster",
    "Warsaw circle", "Whitehead theorem", "CW complex",
    "Schoenflies problem", "Ida surface", "Riemann surface",
    "Morin surface", "Nielsen–Thurston", "Pinched torus",
    "Simons cone", "Seifert surface", "Seashell surface",
    "Whitney umbrella",
)


def audit(text=None):
    if text is None:
        text = LEDGER.read_text(encoding="utf-8")
    # Accept only the 20 numbered rows of the original acceptance table.
    matches = re.findall(
        r"^\|\s*(\d+)\s*\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|\s*$",
        text, flags=re.MULTILINE,
    )
    rows = [(int(n), name.strip(), available.strip(), missing.strip())
            for n, name, available, missing in matches
            if 1 <= int(n) <= 20]
    assert len(rows) == 20, "the original twenty-object query is not exhausted"
    assert [n for n,*_ in rows] == list(range(1, 21))
    assert tuple(name for _,name,*_ in rows) == EXPECTED_OBJECTS
    assert all(len(a) >= 12 and len(m) >= 12 for _,_,a,m in rows)
    assert all(any(x in a for x in ("F:", "S:", "D:", "R:", "OPEN"))
               for _,_,a,_ in rows)
    assert "None of these twenty source-specific hallmark tasks" in text
    assert "kernel receipt" in text
    assert "Source identity:" in text
    assert "Same-object realisation:" in text
    assert "Discriminating theorem:" in text
    assert "Kernel/paper proof receipt:" in text
    assert "Brahana (1921)" in text and "Power (2025)" in text
    assert "2024 preprint" in text and "one" in text
    for phase in range(6):
        assert f"**{phase} —" in text, f"missing independent phase gate {phase}"
    return {
        "status":"PASS nonpromoting acceptance-ledger audit",
        "requested_object_count":len(rows),
        "original_question_completeness_of_inventory":True,
        "kernel_proof_completion_claim":False,
        "phase_count":6,
        "source_root_and_version_disciplines_present":True,
        "row_names":[name for _,name,*_ in rows],
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
