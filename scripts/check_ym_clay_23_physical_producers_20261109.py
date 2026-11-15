#!/usr/bin/env python3
"""Fail-closed 23 physical producer / 10 terminal owner / 5 phase audit.

This validates the documented Clay YM mathematical scope only.
It does NOT typecheck Agda or discharge physical CMP116/E1/OS endpoints.
Run with Python 3 from any repository checkout; no CI dependency.
"""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "Docs/physics/YMClay23PhysicalProducersCurrentMaxCut20261109.md"
PHASE_DOC = ROOT / "Docs/physics/YMClayRoadmapPhasesDeliverablesExactLemmas20261108.md"
MANIFEST = ROOT / "Docs/physics/YMClayEndpointPhaseLemmaManifest20261108.json"
SOURCE = ROOT / "DASHI/Physics/YangMills/YMClayE1D1OriginalVariablePlaquetteWordsExact.agda"
REGRESSION = ROOT / "DASHI/Unified/YMClayOriginalWilsonPhysicalRegression.agda"
GROUPS = {"E1": 7, "D1": 4, "D2": 5, "N1": 3, "G1": 4}

def main():
    ledger = LEDGER.read_text(encoding="utf-8")
    phases = PHASE_DOC.read_text(encoding="utf-8")
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    code = SOURCE.read_text(encoding="utf-8")
    root = REGRESSION.read_text(encoding="utf-8")
    ids = re.findall(r"^\| (E1|D1|D2|N1|G1)\.(\d{2})\b", ledger, re.M)
    ids = [f"{prefix}.{digits}" for prefix, digits in ids]
    expected = {
        f"{prefix}.{i:02d}"
        for prefix, count in GROUPS.items()
        for i in range(1, count + 1)
    }
    assert len(ids) == len(set(ids)) == len(expected) == 23
    assert set(ids) == expected, (sorted(expected - set(ids)), sorted(set(ids) - expected))
    owners = {x["id"] for x in manifest["lemmas"]}
    assert owners == {f"YM{i:02d}" for i in range(1, 11)}
    phase_ids = {x["id"] for x in manifest["phases"]}
    assert phase_ids == {f"PH{i}" for i in range(5)}
    assert manifest["terminal_status"] != "existing_source_written"
    for p in manifest["phases"]:
        assert p["lemmas"] and set(p["lemmas"]).issubset(owners)
        assert f"**{p['id']}" in phases, p["id"]
    for name in [
        "originalAllLengthWordsAreGaugeInvariant",
        "originalChangingWordGaugeInvariant",
        "originalAllLengthWordE1D1CovarianceIdentity",
        "originalAllLengthWordMixedJetIsD1Covariance",
        "Cumulant.sourceDirectionOf",
    ]:
        assert name in code, name
    assert "YMClayE1D1OriginalVariablePlaquetteWordsExact" in root
    for name in ["YMClayD1OriginalRealCMP116VariableCutoffExact",
                 "YMClayD1OriginalFullWilsonSmallLargeFieldExact",
                 "D1.03", "D2.03", "G1.03"]:
        assert name in ledger, name
    print("PASS: 23 unique E1/D1/D2/N1/G1 producer IDs")
    print("PASS: 10 terminal YM01-YM10 owners and 5 PH0-PH4 phases")
    print("PASS: original real all-word E1/D1 regression and jet directions")
    print("SCOPE: documentation/source guard only; no physical theorem acceptance")

if __name__ == "__main__":
    main()
