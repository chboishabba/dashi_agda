#!/usr/bin/env python3
"""Static source-owner and litigation gate audit; NOT real-law proof or Agda execution."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LAW = ROOT / "DASHI/Law/SensibLawWoogarooStandingTimeInterimCounselTriage20261027Exact.agda"
PREVIOUS = ROOT / "DASHI/Law/SensibLawWoogarooEPBC95C135ADecisionFileMaxCut20261027Exact.agda"
ROLLUP = ROOT / "DASHI/Law/SensibLawWoogarooPreservationEverything.agda"
COUNSEL = ROOT / "Docs/SaveWoogarooForestUrgentCounselStandingFilingInterimAssessment20261027.md"
EPO_DRAFT = ROOT / "Docs/SaveWoogarooNationalEPA474AConditionalRegulatorNotice20261027.md"
LEGAL_TEAM = ROOT / "Docs/SaveWoogarooForestLegalTeamBrief.md"
REQUEST = ROOT / "Docs/SaveWoogarooForestEPBC95C135ARequest20261027.md"
RESEARCH = ROOT / "docs/research/WoogarooPostApprovalGasHousingBenefitMaxCut20261027.md"
OFT_REQUEST = ROOT / "Docs/SaveWoogarooForestOFTStandingEvidenceRequest20261028.md"

TOPICS = [
    "EPBC identity", "1997 Springfield DCP", "9281/9293", "functional cumulative",
    "Habitat/koala", "signatory", "Santoro", "Cherish/Stockland",
    "Housing policy/HAFF", "First/second/third-order", "Utility infrastructure",
    "Orion/BlackRock", "Polaris", "standing/time/interim", "Court proceeding",
    "Authorship", "Santos/Santoro", "Scenic Precinct",
    "QUT legal-academics", "National EPA compliance order"
]

def main() -> None:
    assert all(p.is_file() for p in (LAW, PREVIOUS, ROLLUP, COUNSEL, REQUEST, RESEARCH, EPO_DRAFT, LEGAL_TEAM, OFT_REQUEST))
    law, previous, rollup, memo, request, research, epo, brief, oft = [
        p.read_text(encoding="utf-8")
        for p in (LAW, PREVIOUS, ROLLUP, COUNSEL, REQUEST, RESEARCH, EPO_DRAFT, LEGAL_TEAM, OFT_REQUEST)
    ]
    assert law.count("Source.mkNoDOISource") == 22
    assert law.count("Source.publicAttribution") == 22
    assert law.count("= litigation-gate") == 25
    assert law.count("→ ⊥") == 28
    assert law.count("false refl") == 25
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
                 "nationalEPA474AEnforcement", "nationalEPAComplianceReport",
                 "qccSameCaseSubmissionLead", "swfgScenicStandingActivityLead",
                 "possinghamScenicActivityLead", "zdenekScenicActivityLead",
                 "swfgABNOrganisationIdentityLead", "swfgMarch2025PublicPetitionLead",
                 "swfgJuly2025CampaignSeriesLead",
                 "qldOFTRulesDecisionDateCut", "qldOFTVersionAndFeeCut",
                 "filedStandingComparatorCut", "acfConstitutionActivitiesComparatorCut",
                 "proponentInboxMarch2026Cut"):
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
                        "lawfulClearingNotAutomaticallyEPOCase",
                        "scenicNotSpringviewComment", "oneLetterNotSection487Series",
                        "originalDateBeatsCaption", "qccNotSwfgStanding",
                        "abnNoObjectsCertification", "senateThemeNotGroupOrganiser",
                        "noDefaultSWFGRules", "notRetrospectiveAssociationObjects",
                        "otherCaseFormNotSWFGStanding", "pleadingNotJudgment",
                        "invitationNotDeliveredComments", "paidFileRequestNotTimeStop"):
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
    assert "import DASHI.Law.SensibLawWoogarooKoalaPopulationConnectivitySnowballExact as Koala" in law
    assert "qutLegalAcademicsMarch2026 = Koala.qutCurrentSubmission" in law
    assert "qccSpringviewMarch2026 = Koala.qccCurrentSubmission" in law
    assert "scenicGroupDecember2025" in law and "15 December 2025" in law
    assert "scenicPossinghamJanuary2025" in law and "4 January 2025" in law
    assert "scenicZdenekDecember2025" in law and "14 December 2025" in law
    assert "no visible wet-ink signature" in law or "not a visible wet-ink signature" in law
    assert "Source.academicArticleSource" not in law
    assert law.count("Source.practitionerSource") >= 4
    assert "EPBC 2020/8651" in law and "EPBC 2019/8575" in law
    assert "originalDateBeatsCaption" in law and "qccNotSwfgStanding" in law
    assert "swfgAustralianBusinessRegister" in law and "86 248 330 120" in law
    assert "17 November 2024" in law and "Other Incorporated Entity" in law
    assert "senateWoogarooPetition2025" in law and "26 March 2025" in law
    assert "ipswichJuly2025CampaignCoverage" in law and "17 July 2025" in law
    assert "abnNoObjectsCertification" in law and "senateThemeNotGroupOrganiser" in law
    assert "National EPA compliance order" in memo
    assert "EPBC s474A" in memo
    assert "27 October 2026 CURRENT STATUS" in brief
    assert "APPROVED WITH CONDITIONS on 15 October 2026" in brief
    assert "## 15 September 2026" in brief  # dated historical snapshot preserved
    assert "Unsent EDO/barrister intake" in brief
    assert "EPBC s474A Environment Protection Order" in brief
    assert "20-row case matrix" in brief
    assert "28 October primary-source standing and filing-precedent upgrade" in memo
    assert "OFTStandingEvidenceRequest20261028" in brief
    assert "NOT SENT" in oft and "28 October 2026" in oft
    assert "VID1357/2025" in oft and "VID1356/2025" in oft and "VID1400/2025" in oft
    assert "epbc@springfieldresidential.com" in oft
    assert "4.20" in oft and "28.85" in oft and "10 working days" in oft
    assert "qldOFTAssociationFileAcquisition" in law
    assert "federalCourtFriendsRockArt2026Form66" in law
    assert "federalCourtACF2026Form66" in law
    assert "springfieldFeb2026CommentInvitation" in law
    assert "qldOFT2026Fees" in law
    assert "noDefaultSWFGRules" in law and "invitationNotDeliveredComments" in law


    assert "Source.mkNoDOISource" not in memo

    for topic in TOPICS:
        assert topic in memo, "missing coverage: " + topic

    print("PASS: twenty-two local original-source records (two canonical aliases), twenty-five unpaid counsel gates, twenty-eight anti-promotion guards and twenty topic coverage cells")


if __name__ == "__main__":
    main()
