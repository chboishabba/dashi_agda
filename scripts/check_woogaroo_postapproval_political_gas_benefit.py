#!/usr/bin/env python3
"""Static source-contract checks for the 27 Oct 2026 Woogaroo post-approval owner.

This checks only source text and stated boundaries. It does NOT execute Agda,
verify political motives, establish gas customers, or assess legal validity.
"""

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
AGDA = ROOT / "DASHI/Law/SensibLawWoogarooPostApprovalPoliticalGasBenefit20261027Exact.agda"
ROLL = ROOT / "DASHI/Law/SensibLawWoogarooPreservationEverything.agda"
ROAD = ROOT / "DASHI/Law/SensibLawWoogarooLegalPriorityRoadmapExact.agda"
NOTE = ROOT / "docs/research/WoogarooPostApprovalGasHousingBenefitMaxCut20261027.md"


def verify() -> None:
    for path in (AGDA, ROLL, ROAD, NOTE):
        assert path.is_file(), f"missing: {path}"
    agda, roll, road, note = (p.read_text(encoding="utf-8") for p in (AGDA, ROLL, ROAD, NOTE))

    assert "module DASHI.Law.SensibLawWoogarooPostApprovalPoliticalGasBenefit20261027Exact where" in agda
    assert "import DASHI.Law.SensibLawSpringfieldGasLobbyingOwnershipSnowballExact as Gas" in agda
    assert "import DASHI.Law.SensibLawWoogarooEPBC8575CumulativeImpactSufficiencyExact as Cumulative" in agda
    assert "import DASHI.Law.SensibLawWoogarooPostApprovalPoliticalGasBenefit20261027Exact" in roll

    assert agda.count("Source.mkNoDOISource") == 8
    assert agda.count("Source.publicAttribution") == 8
    assert agda.count("= scoped-receipt") == 7
    assert agda.count("false refl") >= 7
    assert agda.count("→ ⊥") == 7
    assert all(s in agda for s in (
        "15 October 2026", "1786", "21 August 2026",
        "30 April 2004", "4 February 2025", "14 October 2026",
        "thirdPartyIndexOnly", "historicConnectionNotCurrentEstate",
        "stateMeetingNotCommonwealthCausation", "housingNarrativeNotImproperInfluence",
        "portalNoticeNotJudicialValidity", "websiteNotLandTitle",
        "thirdPartyIndexNotDispositive", "proposedBillNotLocalSubsidy",
    ))

    federal = road.split("federal8575Priority :", 1)[1].split("federalClockReceipt :", 1)[0]
    assert "15 October 2026" in federal
    assert "APPROVED WITH CONDITIONS" in federal
    assert "1 October 2026 deadline" not in federal
    assert "urgent counsel" in federal
    assert "section 135A" in federal
    assert "date" in federal

    assert all(s in note for s in (
        "1,786 comments", "more than 850 submissions", "2020/8651",
        "2004", "third-party index", "all-electric counterfactual",
        "section 135A", "15 October 2026", "original",
        "not a legal opinion", "historical infrastructure",
    ))
    assert re.search(r"\\bP0\\b", note) and re.search(r"\\bP4\\b", note)
    assert "NOT the actual final preliminary documentation" in note
    print("PASS: source-text evidence, time, jurisdictions, seven promotion firewalls, seven scoped receipts")


if __name__ == "__main__":
    verify()
