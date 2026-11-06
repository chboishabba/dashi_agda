#!/usr/bin/env python3
"""Static contract: EPBC 2019/8575 s95B-s95C-s135A legal-document consumer.

Checks textual invariants only. Does not certify Agda, execute review,
verify delivery of original records, or establish any judicial-review ground.
"""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OWNER = ROOT / "DASHI/Law/SensibLawWoogarooEPBC95C135ADecisionFileMaxCut20261027Exact.agda"
ROLLUP = ROOT / "DASHI/Law/SensibLawWoogarooPreservationEverything.agda"
ROADMAP = ROOT / "DASHI/Law/SensibLawWoogarooLegalPriorityRoadmapExact.agda"
REQUEST = ROOT / "Docs/SaveWoogarooForestEPBC95C135ARequest20261027.md"
STUDY = ROOT / "docs/research/WoogarooPostApprovalGasHousingBenefitMaxCut20261027.md"


def check() -> None:
    assert all(p.is_file() for p in (OWNER, ROLLUP, ROADMAP, REQUEST, STUDY))
    owner, roll, road, request, study = (
        p.read_text(encoding="utf-8") for p in (OWNER, ROLLUP, ROADMAP, REQUEST, STUDY)
    )

    assert owner.count("Source.mkNoDOISource") == 5
    assert owner.count("Source.publicAttribution") == 5
    assert owner.count("= decision-file-receipt") == 13
    assert owner.count("→ ⊥") == 11
    assert owner.count("false refl") == 13
    assert roll.count("import DASHI.Law.SensibLawWoogarooEPBC95C135ADecisionFileMaxCut20261027Exact") == 1

    for label in ("95B(1)", "95C(1)", "135A(2)", "136(1)", "139",
                  "15 October 2026", "22 October 2026",
                  "National Environmental Standards", "1 December 2026"):
        assert label in owner or label in study, label

    assert "section95BActualComments" in owner
    assert "section95BResponse" in owner
    assert "section95CRecommendation" in owner
    assert "section135AStatutoryRequest" in owner
    assert "section136Housing" in owner
    assert "section139SpeciesAdvice" in owner
    assert "signedConditions" in owner
    assert "adjrApplicantSpecificClock" in owner
    assert "adjrStandingLinkedReasons" in owner

    for guard in (
        "listingDoesNotPaySignedNotice",
        "registeredStandardsNotAutomaticallyOperative",
        "section95CNotApprovalNotice",
        "commentCountNotTransmissionReceipt",
        "portfolioNotPersonalSignature",
        "socialFactorNotCorruption",
        "existenceNotReviewGround",
        "futureRuleNotPastRule",
        "portalNoticeNotApplicantFurnishing",
        "reportRequestDoesNotStayFilingLimit",
        "section13DifferentRequesterClass",
    ):
        assert guard in owner, guard

    assert "section 95C recommendation report requested under section 135A(2)" in road
    assert "section 95B" in road
    assert "Item 4.6(c)" in road
    assert "draft, not sent" in request
    assert "Sending this request does NOT apply for judicial review" in request
    assert "s135A(2)" in request
    assert "Section 11(1)(c), (3)" in request
    assert "Section 13(1), (5), (11)" in request
    assert "s95B" in request
    assert "1,786" in request
    assert "operative" in study and "15 October" in study

    print("PASS: 5 original statute/agency roots; 13 documentary atoms; 11 no-promotion guards; unsent statutory request")


if __name__ == "__main__":
    check()
