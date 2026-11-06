#!/usr/bin/env python3
"""Fail-closed #1460 exact physical producer count and scope audit.

40 names = 10 OBS + 12 HIL + 10 KK + 8 BIDI.
These are producer obligations, NOT additional canonical lemmas and NOT
the 48 independent phased execution tasks. The authoritative 186-ID
checker remains scripts/check_tsfv_unification_48_phase_cut_20261106.py.
This checks documentation, not Agda kernel acceptance or physical truth.
"""
from collections import Counter
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
PRODUCERS = ROOT / "Docs/roadmaps/TSFVFourPhysicalCutsExactProducerLemmas20261106.md"
PHASES = ROOT / "Docs/roadmaps/TSFVUnificationExecutionPhasesDeliverablesExactLemmas20261106.md"
TODO = ROOT / "Docs/roadmaps/TSFVUnificationTODO20261106.md"
RECEIPT = ROOT / "Docs/physics/TSFVUnificationMaxCutImplementationReceipt20261106.md"
EXPECTED = {"OBS": 10, "HIL": 12, "KK": 10, "BIDI": 8}
ROW = re.compile(
    r"^\| \*\*(OBS|HIL|KK|BIDI)(\d{2})\*\* — `([^\x60]+)`"
    r" \| `([^\x60]+)` \| ([^|]+) \|$",
    re.MULTILINE,
)
PHASE_ROW = re.compile(r"^\| `([VOHKB]\d{2})` \|", re.MULTILINE)


def main():
    source = PRODUCERS.read_text(encoding="utf-8")
    phases = PHASES.read_text(encoding="utf-8")
    todo = TODO.read_text(encoding="utf-8")
    receipt = RECEIPT.read_text(encoding="utf-8")
    rows = ROW.findall(source)
    observed = [(family, int(index), name) for family, index, name, _, _ in rows]
    assert len(rows) == 40, f"expected 40 producer rows, observed {len(rows)}"
    assert len(set(observed)) == 40, "duplicate producer ID/name"
    for family, expected in EXPECTED.items():
        actual = {int(i) for fam, i, *_ in rows if fam == family}
        assert actual == set(range(1, expected + 1)), (
            family, "missing", sorted(set(range(1, expected + 1)) - actual)
        )
    for family, _, name, canonical, statement in rows:
        assert name.strip() and statement.strip(), family
        assert re.search(r"P\d{2}\.L\d{2}", canonical), (
            family, name, canonical
        )
    execution_ids = PHASE_ROW.findall(phases)
    assert len(execution_ids) == len(set(execution_ids)) == 48
    for doc_name, doc in [
        ("producers", source), ("phases", phases),
        ("todo", todo), ("receipt", receipt),
    ]:
        assert "40 named" in doc or "40 exact" in doc, (
            f"{doc_name}: missing correct 40-producer inventory reference"
        )
        assert "48" in doc, f"{doc_name}: lost independent 48-task reference"
    for required in [
        "TSVFOriginalSelectedFiniteCommutatorResponseExact",
        "TSVFOriginalForwardPositiveFunctionalExact",
        "TSVFOriginalQuantumSurfaceSpatialNonpromotionExact",
        "TSVFOriginalR445ReflectedAllWordGramExact",
        "TSVFOriginalR445PublishedWilsonRPWordWeldExact",
        "KK10",
        "YMClayOriginalWilsonNativeOSPullbackExact",
        "YMClaySUNOriginal64Pair896MarkedEffectiveSourceExact",
        "HIL07", "KK08", "OBS05", "BIDI04",
    ]:
        assert required in source, f"missing canonical source/frontier {required}"
    print("PASS 40 unique exact physical producer obligations:", EXPECTED)
    print("PASS 48 distinct execution tasks; separate from 186 canonical lemmas")
    print("SOURCE DOC AUDIT ONLY: no kernel/physical completion inferred")


if __name__ == "__main__":
    main()
