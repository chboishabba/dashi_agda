#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

EXPECTED = {
    "DASHI/Culture/PowersPlantationParadiseSourceAtlasExact.agda": [
        "powersBookSource", "mondelliReviewSource", "prestRacialScaleSource",
        "prestIphigenieSource", "clayStagestruckSource",
        "theatreSaintDomingueProjectSource", "affichesAmericanesArchiveSource",
        "lamecaSaintDomingueOperaSource", "canonicalPowersSourceBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseHistoricalClaimReceiptsExact.agda": [
        "colonialHierarchyClaimReceipt", "colonialSocietyAtTheTheatreClaimReceipt",
        "introducingStarsClaimReceipt", "breakingBarrierClaimReceipt",
        "escapeFromRealityClaimReceipt", "finaleRevolutionClaimReceipt",
        "InspectionEvidenceCoherent", "pageRangeDoesNotPromoteUninspectedPassage",
    ],
    "DASHI/Culture/ColonialPerformanceStatusNonfactorabilityExact.agda": [
        "performedRoleCannotRecoverSocialOccupancy", "performanceCannotRecoverEndorsement",
    ],
    "DASHI/Culture/HistoricalArchiveAbsenceNonfactorabilityExact.agda": [
        "absenceInArchiveCannotRecoverAbsenceInWorld", "archiveCompletenessRequiresWitness",
    ],
    "DASHI/Culture/ColonialTheatreAccessAdapterExact.agda": [
        "sameProductionCannotRecoverVenueAccess", "historyQualifiedTheatreAccess",
    ],
    "DASHI/Culture/PowersPlantationParadiseGovernedCrossPollinationExact.agda": [
        "sameCulturalSurfaceCannotRecoverStanding", "sameCulturalSurfaceCannotRecoverContestability",
        "sameCulturalSurfaceCannotRecoverMaterialCone", "everyAdequateStandingObserverSeparates",
        "everyAdequateContestabilityObserverSeparates", "everyAdequateMaterialConeObserverSeparates",
        "standingContestabilityJoint", "governedSocialPositionJoint",
        "sameCulturalSurfaceCannotRetainGovernedSocialPosition", "powersLegibilityChannel",
        "powersExactInstitutionalViewDecoderImpossible", "powersChapter5RootedTraceClaim",
    ],
    "DASHI/Culture/PowersPlantationParadiseMinetteMicrohistoryExact.agda": [
        "prestMinetteMarsanSource", "camierMinetteLifeSource",
        "christmas1780ConcertReceipt", "moreauFebruary1781DebutReceipt",
        "march1781BenefitReceipt", "zemire1783BenefitReceipt", "nina1787BenefitReceipt",
        "minette1789LegalDisputeReceipt", "MinetteSalaryNonpaymentReceipt",
        "minette1784SalaryNonpaymentReceipt", "contractAndNonpaymentDoNotProveSettlement",
        "prestLegalNoticeDateReceipt", "lamecaLegalNoticeDateReceipt",
        "secondaryDateDisagreementNeedsPrimaryInspection", "benefitPerformanceDoesNotProveSettlement",
        "canonicalMinetteMicrohistoryBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseMinetteChronologyContestationExact.agda": [
        "minette1790NoticeRoot", "prest1790ClaimLeaf", "lameca1790ClaimLeaf",
        "minette1790NoticeContestationRelation", "canonicalMinetteChronologyContestationBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseEnslavedDistributionEvidenceExact.agda": [
        "prest2023EnslavedTheatreSource", "prest2023DistributionEvidence",
        "capViolinists1764ContributionBurdenReceipt", "julien1781ContributionBurdenReceipt",
        "contributionBurdenJoinDoesNotCompleteBenefitVoice",
        "canonicalPowersEnslavedDistributionEvidenceBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadisePerformerComparisonExact.agda": [
        "prestTransnationalPerformanceSource", "liseSaintMarc1786Receipt",
        "minetteTrajectorySurface", "liseTrajectorySurface",
        "siblingComparisonDoesNotPayCausalCounterfactual",
        "canonicalPowersPerformerComparisonBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseComparativeVenueEvidenceExact.agda": [
        "saintPierre1786PlannedSeatingReceipt", "isertSaintPierreObservedPricingReceipt",
        "martiniqueEvidenceDoesNotTransportSaintDomingueRule",
        "canonicalPowersComparativeVenueEvidenceBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseEmpiricalProgrammeExact.agda": [
        "minetteCareerStatusReceipt", "portAuPrinceSeatingGeometryReceipt",
        "portAuPrinceFloorplanReceipt", "portAuPrinceBusinessReceipt",
        "theatreCorpusProvenanceReceipt", "benefitBurdenBoundary", "responsibilityBurdenBoundary",
        "namedPerformerStatusLeaf", "venueSeatingAccessLeaf", "venueEconomyLeaf",
        "distributionalIncidenceLeaf", "causalMobilityLeaf", "primaryCorpusSaturationLeaf",
        "compensationPaymentLeaf", "legalStatusSeatingRuleLeaf",
        "theatreParticipationMobilityCausalDemand", "observationalEvidenceDoesNotIdentifyCausalEffect",
        "canonicalPowersEmpiricalProgrammeBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseEmpiricalAcquisitionParetoExact.agda": [
        "primaryCorpusCell", "compensationLedgerCell", "distributionalIncidenceCell",
        "causalIdentificationCell", "empiricalAcquisitionFrontier",
        "currentFrontierIsCorpusDistribution", "compensationLedgerOffCurrentFrontier",
        "canonicalPowersEmpiricalAcquisitionParetoBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseSynthesisExact.agda": [
        "paradiseObserverCannotRecoverMaterialAffordance", "recognitionCannotRecoverDistribution",
        "localExpansionDoesNotProveGlobalEmancipation", "sourceClaimDoesNotBecomeDASHITheorem",
        "historicalClaimBoundary", "governedCrossPollinationBoundary",
        "empiricalProgrammeBoundary", "empiricalAcquisitionParetoBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseValidation.agda": [
        "_paradise-material-gap-paid", "_performance-status-gap-paid", "_archive-absence-gap-paid",
        "_governed-standing-gap-paid", "_contestability-gap-paid", "_material-cone-gap-paid",
        "_joint-required-axes-gap-paid", "_governed-social-position-gap-paid",
        "_legibility-decoder-gap-paid", "_empirical-minette-receipt-paid",
        "_empirical-seating-receipt-paid", "_empirical-causal-firewall-paid",
        "_empirical-acquisition-frontier-paid", "_minette-salary-nonpayment-paid",
        "_minette-date-contestation-paid", "_enslaved-distribution-category-evidence-paid",
        "_julien-contribution-burden-paid", "_lise-saint-marc-event-paid",
        "_sibling-comparison-not-causal-control-paid", "_martinique-comparative-seating-paid",
        "_martinique-not-saint-domingue-rule-paid", "_rooted-trace-paid",
    ],
}

errors = []
for rel, markers in EXPECTED.items():
    path = ROOT / rel
    if not path.exists():
        errors.append(f"missing file: {rel}")
        continue
    text = path.read_text(encoding="utf-8")
    for marker in markers:
        if marker not in text:
            errors.append(f"{rel}: missing marker {marker}")

rollup = ROOT / "DASHI/Culture/Everything.agda"
if not rollup.exists():
    errors.append("missing Culture/Everything.agda")
else:
    lines = set(rollup.read_text(encoding="utf-8").splitlines())
    for module in [
        "PowersPlantationParadiseSourceAtlasExact", "PowersPlantationParadiseHistoricalClaimReceiptsExact",
        "ColonialPerformanceStatusNonfactorabilityExact", "HistoricalArchiveAbsenceNonfactorabilityExact",
        "ColonialTheatreAccessAdapterExact", "PowersPlantationParadiseGovernedCrossPollinationExact",
        "PowersPlantationParadiseMinetteMicrohistoryExact",
        "PowersPlantationParadiseMinetteChronologyContestationExact",
        "PowersPlantationParadiseEnslavedDistributionEvidenceExact",
        "PowersPlantationParadisePerformerComparisonExact",
        "PowersPlantationParadiseComparativeVenueEvidenceExact",
        "PowersPlantationParadiseEmpiricalProgrammeExact",
        "PowersPlantationParadiseEmpiricalAcquisitionParetoExact",
        "PowersPlantationParadiseSynthesisExact", "PowersPlantationParadiseValidation",
    ]:
        if f"import DASHI.Culture.{module}" not in lines:
            errors.append(f"Culture/Everything.agda missing import {module}")

if errors:
    raise SystemExit("\n".join(errors))

print("Plantation to Paradise empirical max-cut static contract: OK")
