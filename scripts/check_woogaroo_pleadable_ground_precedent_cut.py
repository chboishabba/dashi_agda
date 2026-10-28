#!/usr/bin/env python3
"""Source-text contract for case construction; not a court judgment, Agda run or proof of legal defect."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OWNER = ROOT / "DASHI/Law/SensibLawWoogarooEPBC8575PleadableGroundsPrecedentCut20261028Exact.agda"
CANON = ROOT / "DASHI/Law/SensibLawWoogarooPreservationEverything.agda"
MEMO = ROOT / "Docs/SaveWoogarooForestPleadableGroundsAndAdversePrecedentCut20261028.md"
COUNSEL = ROOT / "Docs/SaveWoogarooForestUrgentCounselStandingFilingInterimAssessment20261027.md"
LEGAL = ROOT / "Docs/SaveWoogarooForestLegalTeamBrief.md"
OLD_MERITS = ROOT / "DASHI/Law/SensibLawWoogarooEPBC20198575OperativeMeritsRulesExact.agda"
OLD_CUMULATIVE = ROOT / "DASHI/Law/SensibLawWoogarooEPBC8575CumulativeImpactSufficiencyExact.agda"
OLD_PRESTART = ROOT / "DASHI/Law/SensibLawWoogaroo9281Condition6aEvidenceStateExact.agda"
OLD_COUNSEL = ROOT / "DASHI/Law/SensibLawWoogarooStandingTimeInterimCounselTriage20261027Exact.agda"
OLD_DOCUMENTS = ROOT / "DASHI/Law/SensibLawWoogarooEPBC95C135ADecisionFileMaxCut20261027Exact.agda"

ORIGINALS = (OWNER, CANON, MEMO, COUNSEL, LEGAL,
             OLD_MERITS, OLD_CUMULATIVE, OLD_PRESTART, OLD_COUNSEL, OLD_DOCUMENTS)

def main() -> None:
    assert all(p.is_file() for p in ORIGINALS)
    owner, canon, memo, counsel, legal, merits, cumulative, prestart, prior_counsel, prior_documents = (
        p.read_text(encoding="utf-8") for p in ORIGINALS
    )
    assert owner.count("Source.mkNoDOISource") == 8
    assert owner.count("Source.publicAttribution") == 8
    assert owner.count("= case-hypothesis") == 7
    assert owner.count("false refl") == 7
    assert owner.count("→ ⊥") == 10
    assert canon.count("import DASHI.Law.SensibLawWoogarooEPBC8575PleadableGroundsPrecedentCut20261028Exact") == 1

    for p in (
        "import DASHI.Law.SensibLawWoogarooEPBC20198575OperativeMeritsRulesExact as Merits",
        "import DASHI.Law.SensibLawWoogarooEPBC8575CumulativeImpactSufficiencyExact as Cumulative",
        "import DASHI.Law.SensibLawWoogaroo9281Condition6aEvidenceStateExact as Condition",
        "import DASHI.Law.SensibLawWoogarooStandingTimeInterimCounselTriage20261027Exact as Counsel",
        "import DASHI.Law.SensibLawWoogarooEPBC95C135ADecisionFileMaxCut20261027Exact as File",
        "canonicalMerits139 = Merits.s139",
        "canonicalMerits136 = Merits.s136",
        "canonicalCumulativeResidual = Cumulative.locatedLocalRegionalIntegrationResidual",
        "canonicalCondition6aSubmission = Condition.condition6aLiteralSubmission",
        "canonicalCondition6aAcceptance = Condition.condition6aCouncilAcceptance",
        "canonicalStandingUnpaid = Counsel.organisationStanding",
        "canonicalSecretaryReportUnpaid = File.section95CRecommendation",
        "import DASHI.Law.SensibLawWoogarooPostApprovalPoliticalGasBenefit20261027Exact as Post",
        "canonicalStocklandFirstPartyDefence = Post.stocklandSpringview"
    ):
        assert p in owner, "missing reused proof/evidence owner: " + p

    for source in (
        "koala2022ApprovedConservationAdvice", "koala2022NationalRecoveryPlan",
        "australianGovernmentSolicitor2024",
        "tarkine2013FederalCourtOriginalJudgmentSummary",
        "tarkine2015FullCourtAdverse",
        "eccq2024FullCourtPrimary",
        "rainforest2025Dismissal",
        "epbcTransitionDepartmentOriginal"
    ):
        assert source in owner, source

    for ground in ("adviceGround", "recoveryGround", "actionImpactGround",
                   "commentsGround", "scopeGround", "localPrestartGround", "politicalTheory"):
        assert ground in owner, ground

    for guard in ("regionalHarmNotOwnProjectImpact", "distinctTarkineDecisions",
                  "practitionerSummaryNotCourtJudgment", "recoveryAimNotAbsoluteProhibition",
                  "adviceURLNotConsideration", "notPublicNotNecessarilyAbsent",
                  "guidanceNotCommencementMatrix", "differentWindFarmDoesNotDecideWoogaroo",
                  "sourceHypothesesNotFiled", "developerClaimNotRegulatorFinding"):
        assert guard in owner, guard

    assert "Merits.s139" in owner and "s139 : OperativeRule" in merits
    assert "Cumulative.locatedLocalRegionalIntegrationResidual" in owner and "locatedLocalRegionalIntegrationResidual :" in cumulative
    assert "Condition.condition6aCouncilAcceptance" in owner and "condition6aCouncilAcceptance :" in prestart
    assert "Counsel.organisationStanding" in owner and "organisationStanding :" in prior_counsel
    assert "File.section95CRecommendation" in owner and "section95CRecommendation :" in prior_documents

    for claim in (
        "[2013] FCA 694", "[2015] FCAFC 89", "[2024] FCAFC 56",
        "[2025] FCA 532", "2022 endangered-koala", "12 February 2022",
        "s139(2)", "s139(1)", "s136(2)(e)", "2019/8575", "2020/8651",
        "F2026L01106", "1 ha", "Item 4.6(c)",
    ):
        assert claim in memo, claim
    assert "28 October precedent steelman and rebuttal" in counsel
    assert "28 October P0 case-ground steelman" in legal
    assert "Stockland Springview primary project FAQ" in memo
    assert "three times the Ipswich minimum width" in memo
    assert "DeveloperFAQEqualsCommonwealthScientificFinding" in owner
    assert "zero of seven grounds" in memo
    assert "NOT counsel's signed opinion" in memo
    assert "not a 2019/8575 ruling" in owner
    assert "failClosed : establishedSpecificBreach ≡ false" in owner
    print("PASS: 8 original source roots, 7 fail-closed candidate grounds, 10 non-promotion guards, 6 canonical owner imports and case-source coverage")


if __name__ == "__main__":
    main()
