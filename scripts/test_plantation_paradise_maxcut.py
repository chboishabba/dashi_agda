#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

EXPECTED = {
    "DASHI/Culture/PowersPlantationParadiseSourceAtlasExact.agda": [
        "powersBookSource",
        "mondelliReviewSource",
        "prestRacialScaleSource",
        "prestIphigenieSource",
        "clayStagestruckSource",
        "theatreSaintDomingueProjectSource",
        "affichesAmericanesArchiveSource",
        "lamecaSaintDomingueOperaSource",
        "canonicalPowersSourceBoundary",
        "chapter3ColonialSocietyAtTheTheatrePages",
        "chapter4IntroducingTheStarsPages",
        "chapter5BreakingThroughBarrierPages",
        "chapter6EscapeFromRealityPages",
        "chapter7FinalePages",
    ],
    "DASHI/Culture/PowersPlantationParadiseHistoricalClaimReceiptsExact.agda": [
        "colonialHierarchyClaimReceipt",
        "colonialSocietyAtTheTheatreClaimReceipt",
        "introducingStarsClaimReceipt",
        "breakingBarrierClaimReceipt",
        "escapeFromRealityClaimReceipt",
        "finaleRevolutionClaimReceipt",
        "InspectionEvidenceCoherent",
        "politicsAndPowerInspectionCoherent",
        "introducingStarsInspectionCoherent",
        "breakingBarrierInspectionCoherent",
        "escapeFromRealityInspectionCoherent",
        "finaleRevolutionInspectionCoherent",
        "pageRangeDoesNotPromoteUninspectedPassage",
    ],
    "DASHI/Culture/ColonialPerformanceStatusNonfactorabilityExact.agda": [
        "performedRoleCannotRecoverSocialOccupancy",
        "performanceCannotRecoverEndorsement",
    ],
    "DASHI/Culture/HistoricalArchiveAbsenceNonfactorabilityExact.agda": [
        "absenceInArchiveCannotRecoverAbsenceInWorld",
        "archiveCompletenessRequiresWitness",
    ],
    "DASHI/Culture/ColonialTheatreAccessAdapterExact.agda": [
        "sameProductionCannotRecoverVenueAccess",
        "historyQualifiedTheatreAccess",
    ],
    "DASHI/Culture/PowersPlantationParadiseGovernedCrossPollinationExact.agda": [
        "sameCulturalSurfaceCannotRecoverStanding",
        "sameCulturalSurfaceCannotRecoverContestability",
        "sameCulturalSurfaceCannotRecoverMaterialCone",
        "everyAdequateStandingObserverSeparates",
        "everyAdequateContestabilityObserverSeparates",
        "everyAdequateMaterialConeObserverSeparates",
        "standingContestabilityJoint",
        "governedSocialPositionJoint",
        "candidateRetainingAllThreeRetainsJointPosition",
        "sameCulturalSurfaceCannotRetainStandingAndContestability",
        "sameCulturalSurfaceCannotRetainGovernedSocialPosition",
        "requiredObserverAxisJoinBoundary",
        "powersLegibilityChannel",
        "powersAsymmetricLegibilityGap",
        "powersExactInstitutionalViewDecoderImpossible",
        "powersContestabilityInterface",
        "expandedInstitutionalContestabilityReceipt",
        "asymmetricLegibilityBoundary",
        "powersChapter5RootedTraceClaim",
        "governedObservationBoundary",
        "recognitionConstitutionBoundary",
        "politicalContestabilityBoundary",
        "historyEcologyOptionConeBoundary",
        "languageUseStandingBoundary",
        "situatedFormalisationBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseEmpiricalProgrammeExact.agda": [
        "minetteCareerStatusReceipt",
        "portAuPrinceSeatingGeometryReceipt",
        "portAuPrinceFloorplanReceipt",
        "portAuPrinceBusinessReceipt",
        "theatreCorpusProvenanceReceipt",
        "benefitBurdenBoundary",
        "responsibilityBurdenBoundary",
        "namedPerformerStatusLeaf",
        "venueSeatingAccessLeaf",
        "venueEconomyLeaf",
        "distributionalIncidenceLeaf",
        "causalMobilityLeaf",
        "primaryCorpusSaturationLeaf",
        "compensationPaymentLeaf",
        "legalStatusSeatingRuleLeaf",
        "theatreParticipationMobilityCausalDemand",
        "observationalEvidenceDoesNotIdentifyCausalEffect",
        "canonicalPowersEmpiricalProgrammeBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseEmpiricalAcquisitionParetoExact.agda": [
        "primaryCorpusCell",
        "compensationLedgerCell",
        "distributionalIncidenceCell",
        "causalIdentificationCell",
        "empiricalAcquisitionFrontier",
        "currentFrontierIsCorpusCompensationDistribution",
        "canonicalPowersEmpiricalAcquisitionParetoBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseSynthesisExact.agda": [
        "paradiseObserverCannotRecoverMaterialAffordance",
        "recognitionCannotRecoverDistribution",
        "localExpansionDoesNotProveGlobalEmancipation",
        "sourceClaimDoesNotBecomeDASHITheorem",
        "historicalClaimBoundary",
        "governedCrossPollinationBoundary",
        "empiricalProgrammeBoundary",
        "empiricalAcquisitionParetoBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseValidation.agda": [
        "_paradise-material-gap-paid",
        "_performance-status-gap-paid",
        "_archive-absence-gap-paid",
        "_governed-standing-gap-paid",
        "_contestability-gap-paid",
        "_material-cone-gap-paid",
        "_joint-required-axes-gap-paid",
        "_governed-social-position-gap-paid",
        "_legibility-decoder-gap-paid",
        "_empirical-minette-receipt-paid",
        "_empirical-seating-receipt-paid",
        "_empirical-causal-firewall-paid",
        "_empirical-acquisition-frontier-paid",
        "_rooted-trace-paid",
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
        "PowersPlantationParadiseSourceAtlasExact",
        "PowersPlantationParadiseHistoricalClaimReceiptsExact",
        "ColonialPerformanceStatusNonfactorabilityExact",
        "HistoricalArchiveAbsenceNonfactorabilityExact",
        "ColonialTheatreAccessAdapterExact",
        "PowersPlantationParadiseGovernedCrossPollinationExact",
        "PowersPlantationParadiseEmpiricalProgrammeExact",
        "PowersPlantationParadiseSynthesisExact",
        "PowersPlantationParadiseValidation",
    ]:
        import_line = f"import DASHI.Culture.{module}"
        if import_line not in lines:
            errors.append(f"Culture/Everything.agda missing import {module}")

workflow = ROOT / ".github/workflows/plantation-paradise-agda.yml"
if not workflow.exists():
    errors.append("missing focused Plantation-to-Paradise Agda workflow")

if errors:
    raise SystemExit("\n".join(errors))

print("Plantation to Paradise max-cut static contract: OK")
