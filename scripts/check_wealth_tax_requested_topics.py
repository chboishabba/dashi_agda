#!/usr/bin/env python3
"""Fail-closed 42-topic coverage inventory for two user-supplied conversations.

A row checks whether a topic is *explicitly* addressed with a status and
attribution boundary. This test does not prove the truth of sources, verify
legal statements or certify Agda proof terms.

DASHI source-written code: research direction Johl Brown;
OpenAI ChatGPT assistance, 2026-10-27. Prior philosophical/empirical
author ownership remains in the referenced canonical sources.
"""
from __future__ import annotations

from collections import Counter
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
DOC = ROOT / "Docs/economics/WealthTaxOriginalConversationsFullCoverage20261027.md"

ROW = re.compile(
    r"^\| (T[0-9]{2}) \| (COVERED_SOURCE_BOUND|FORMAL_FINITE|OPEN_EMPIRICAL) "
    r"\| ([^\n]+?) \| ([^\n]+?) \|$",
    re.MULTILINE,
)
EXPECTED = {f"T{i:02d}" for i in range(1, 43)}
OWNERS = (
    "DASHI/Economics/WealthInheritanceVacancyTaxMaxCut20261027Exact.agda",
    "DASHI/Economics/WealthTaxPowerCareSociologyBidi20261027Exact.agda",
    "DASHI/Economics/WealthTaxFiscalTransmissionControlBidi20261027Exact.agda",
)
PHILOSOPHY_OR_SOCIETY = (
    "Marx", "Engels", "anarch", "postmodern", "Lyotard", "Baudrillard",
    "accelerationism", "Nick Land", "Varoufakis", "techno", "Federici",
    "Fraser", "Crenshaw", "Collins", "Yarvin", "blackpill", "Doomer",
    "fourth-wave", "Pareto",
)
POLICY_AND_HISTORY = (
    "Musk", "Piketty", "Henry George", "Adam Smith", "Roosevelt",
    "94%", "buy, borrow, die", "Vancouver", "Victoria", "AI",
    "inheritance", "Samsung", "Pillar Two", "UK SDRT",
    "Beneficial ownership", "tax assessed", "tax collected",
    "causal", "Ibrahim",
)

def main() -> None:
    text = DOC.read_text(encoding="utf-8")
    rows = ROW.findall(text)
    observed = Counter(id for id, _, _, _ in rows)
    missing = EXPECTED - observed.keys()
    unexpected = observed.keys() - EXPECTED
    duplicates = {id: count for id, count in observed.items() if count != 1}
    assert not missing, f"Missing requested topic IDs: {sorted(missing)}"
    assert not unexpected, f"Unknown topic IDs: {sorted(unexpected)}"
    assert not duplicates, f"Duplicate topic IDs: {duplicates}"
    assert len(rows) == 42, f"expected 42 rows, got {len(rows)}"
    for id, status, claim, source in rows:
        assert len(claim.strip()) > 35, f"{id} missing substantive scope"
        assert len(source.strip()) > 30, f"{id} missing source/boundary"
        if status == "OPEN_EMPIRICAL":
            assert ("required" in claim.lower() or "not" in claim.lower()
                    or "pending" in claim.lower() or "need" in claim.lower()
                    or "must" in claim.lower() or "uncorroborated" in claim.lower()
                    or "no " in claim.lower()), f"{id}: gap must remain explicit"
    for term in PHILOSOPHY_OR_SOCIETY + POLICY_AND_HISTORY:
        assert term.lower() in text.lower(), f"topic phrase absent: {term}"
    for owner in OWNERS:
        assert (ROOT / owner).is_file(), f"missing live formal owner: {owner}"
    script = (ROOT / "scripts/check_wealth_tax_maxcut.py").read_text(encoding="utf-8")
    for symbol in ("test_finite_caps", "test_assessment_collection_appropriation_are_distinct",
                   "test_dual_class_voting_post_transfer", "test_assessment_vs_interim_growth"):
        assert symbol in script, f"missing bounded regression: {symbol}"
    statuses = Counter(status for _, status, _, _ in rows)
    print(f"PASS: {len(rows)} distinct sourced/typed topic rows; "
          f"statuses {dict(sorted(statuses.items()))}; "
          "three existing Agda owner paths; four Python regression names.")
    print("This is a coverage receipt, NOT a truth or Agda kernel receipt.")

if __name__ == "__main__":
    main()
