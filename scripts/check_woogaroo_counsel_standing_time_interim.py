#!/usr/bin/env python3
"""Static source-owner and litigation gate audit; NOT real-law proof or Agda execution."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LAW = ROOT / "DASHI/Law/SensibLawWoogarooStandingTimeInterimCounselTriage20261027Exact.agda"
PREVIOUS = ROOT / "DASHI/Law/SensibLawWoogarooEPBC95C135ADecisionFileMaxCut20261027Exact.agda"
ROLLUP = ROOT / "DASHI/Law/SensibLawWoogarooPreservationEverything.agda"
COUNSEL = ROOT / "Docs/SaveWoogarooForestUrgentCounselStandingFilingInterimAssessment20261027.md"
EPO_DRAFT = ROOT / "Docs/SaveWoogarooNationalEPA474AConditionalRegulatorNotice20261027.md"
REQUEST = ROOT / "Docs/SaveWoogarooForestEPBC95C135ARequest20261027.md"
RESEARCH = ROOT / "docs/research/WoogarooPostApprovalGasHousingBenefitMaxCut20261027.md"

TOPICS = [
    "EPBC identity", "1997 Springfield DCP", "9281/9293", "functional cumulative",
    "Habitat/koala", "signatory", "Santoro", "Cherish/Stockland",
    "Housing policy/HAFF", "First/second/third-order", "Utility infrastructure",
    "Orion/BlackRock", "Polaris", "standing/time/interim", "Court proceeding",
    "Authorship"
]

def main() -> None:
    assert all(p.is_file() for p in (LAW, PREVIOUS, ROLLUP, COUNSEL, REQUEST, RESEARCH, EPO_DRAFT))
    law, previous, rollup, memo, request, research, epo = [
        p.read_text(encoding="utf-8")
        for p in (LAW, PREVIOUS, ROLLUP, COUNSEL, REQUEST, RESEARCH, EPO_DRAFT)
    ]
    assert law.count("Source.mkNoDOISource") == 11
    assert law.count("Source.publicAttribution") == 11
    assert law.count("= litigation-gate") == 13
    assert law.count("→ ⊥") == 16
    assert law.count("false refl") == 13
    assert rollup.count("import DASHI.Law.SensibLawWoogarooStandingTimeInterimCounselTriage20261027Exact") == 1

    assert "import DASHI.Law.SensibLawWoogarooEPBC95C135ADecisionFileMaxCut20261027Exact as File" in law
    assert "import DASHI.Law.SensibLawWoogarooLegalPriorityRoadmapExact as Legal" in law
    assert "import DASHI.Law.SensibLawWoogarooGainLossSnowballAdapterExact as Distribution" in law
    assert "section95CRecommendation" in law
    assert "whoBearsEcologicalLoss" in law
    assert "Legal.federal8575Priority" in law

    # The September 29 law is operative on October 15, NOT C133 August 27.
    assert "C2026C00448" in law and "29 September 2026" in law
    assert "compilation 134" in previous
    assert "29 September 2026" in previous
    assert "original 29 September 2026" in request
    assert "29 September 2026" in research

    for clause in ("s487(2)-(3)", "s475(1),(5)-(7)", "s11(1)(c),(3)-(5)",
                   "s13", "s15", "r31.01", "Form 66", "Form 67", "Form 12",
                   "Certificate of Urgency", "usual undertaking"):
        assert clause in law or clause in memo, clause

    for name in ("individualStanding", "organisationStanding", "independentAffectedInterest",
                 "section39BAlternative", "furnishingClock", "stayAfterFiling",
                 "epbcContravention", "beforeOriginating", "undertakingRisk", "qutLetterEvidenceLead", "campaignActivityLead",
                 "nationalEPA474AEnforcement", "nationalEPAComplianceReport"):
        assert name in law, name

    for noPromotion in ("identityNotStanding", "onlineNoticeNotFurnishing",
                        "requestNotToll", "conditionalApprovalNotAutomaticallyContravention",
                        "habitatNotBreach", "filingDoesNotAutomaticallyStay",
                        "publicInterestNotCostsExemption", "politicsNotGround",
                        "registryNotLegalCounsel", "sourceCodeNotCourtFinding",
                        "addressedLetterNotProvenReceipt", "campaignAppealNotLitigation",
                        "epoPowerNotAutomaticallySiteProtection",
                        "warrengailDifferentFromWoogaroo",
                        "complaintNotCourtOrOrder",
                        "lawfulClearingNotAutomaticallyEPOCase"):
        assert noPromotion in law, noPromotion

    # Actual deadlines, eligibility, completed acts and direct payments stay unpaid.
    assert "resultObtained ≡ false" in law
    assert "12 November 2026" in memo and "hypothetical" in memo
    assert "15 October 2024" in memo and "15 October 2026" in memo
    assert "No automatically available public-interest waiver" in memo or "NO automatically available public-interest waiver" in memo
    assert "draft, not sent" in request and "does NOT apply for judicial review" in request
    assert "judicial review and" in memo.lower() or "federal judicial review" in memo.lower()
    assert "no confirmed original signed" in memo.lower()
    assert "12 March 2026" in memo
    assert "Monica Taylor" in memo and "Rowena Maguire" in memo and "Bridget Lewis" in memo
    assert "2020/8651" in memo and "2019/8575" in memo
    assert "addressedLetterNotProvenReceipt" in law and "campaignAppealNotLitigation" in law
    assert "474A" in epo and "474B" in epo and "474D" in epo
    assert "Warrengail Pastoral Company" in epo and "Wombinoo Station" in epo
    assert "2019/8575" in epo and "2020/8651" not in epo
    assert "NOT SENT" in epo and "no order requested" in epo.lower()
    assert "environment.compliance@nationalepa.gov.au" in epo
    assert "nationalEPAEPOOriginal" in law and "nationalEPARulesOriginal" in law
    assert "nationalEPAReportBreachOriginal" in law
    assert "National EPA compliance order" in memo
    assert "EPBC s474A" in memo

    assert "Source.mkNoDOISource" not in memo

    for topic in TOPICS:
        assert topic in memo, "missing coverage: " + topic

    print("PASS: eleven original-source roots, thirteen unpaid counsel gates, sixteen anti-promotion guards and sixteen topic coverage cells")


if __name__ == "__main__":
    main()
