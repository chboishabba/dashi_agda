#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

EXPECTED = {
    "DASHI/Culture/PowersPlantationParadiseMethodologySourceAtlasExact.agda": [
        "prest2023PublicTheatreSource", "prest2023MethodologySource",
        "prest2024ResponseSource", "row2024ReviewSource", "sabee2024ReviewSource",
        "prest2025DisabilitySource", "freedomOnTheMoveSource",
        "canonicalPowersMethodologySourceBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseArchiveModalityExact.agda": [
        "SourceGenre", "SourceProductionContext", "runawaySaleAdvertisementContext",
        "theatreAnnouncementContext", "notarialWillContext", "policeRuleContext",
        "sameSilenceDifferentProductionContext",
        "sourceGenreDoesNotCreateHistoricalTruth",
        "canonicalPowersArchiveModalityBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseSourceAcquisitionPromotionExact.agda": [
        "ResolutionStage", "HistoricalSourceAcquisitionReceipt",
        "HistoricalSourceAcquisitionObligation",
        "julien1781SecondaryCoordinateReceipt", "minette1784WillSecondaryCoordinateReceipt",
        "lise1786AnnouncementSecondaryCoordinateReceipt",
        "july1790PrimaryIssueObligation", "minetteSettlementObligation",
        "saintDomingueSeatingRuleObligation", "locationCannotRecoverInspection",
        "inspectionCannotRecoverQualification",
        "canonicalPowersSourceAcquisitionPromotionBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseFrontierGenealogyExact.agda": [
        "FrontierGenealogyReceipt", "compensationFrontierGenealogy",
        "distributionFrontierGenealogy", "chronologyFrontierGenealogy",
        "causalFrontierGenealogy", "frontierNarrativeDoesNotCreateHistoricalTruth",
        "canonicalPowersFrontierGenealogyBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadisePromotionGateValidation.agda": [
        "_source-acquisition-boundary-paid", "_frontier-genealogy-boundary-paid",
        "_july-primary-obligation-paid", "_minette-settlement-obligation-paid",
        "_compensation-genealogy-paid", "_distribution-genealogy-paid",
    ],
    "DASHI/Culture/PowersPlantationParadiseInvestigationParetoExact.agda": [
        "primaryCorpusCandidate", "actorDistributionCandidate",
        "compensationSettlementCandidate", "seatingRuleCandidate",
        "causalIdentificationCandidate", "canonicalITIRBoundary",
        "PrimaryIssueChronologyReopening", "primaryIssueReopensChronology",
        "primaryIssueReopensEventLedger", "actorCompensationReopensDistribution",
        "canonicalPowersInvestigationRoutingBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseHistoricalDiscriminatorExact.agda": [
        "seatingOrdinanceRoute", "seatingEnforcementRoute", "minetteSettlementRoute",
        "july1790PrimaryIssueRoute", "actorBenefitRoute", "actorVoiceRoute",
        "powersHistoricalExperimentDesign", "proposedDiscriminatorDoesNotCreateHistoricalTruth",
        "canonicalPowersHistoricalDiscriminatorBoundary",
    ],
    "DASHI/Culture/ColonialTheatreSensoryAccessExact.agda": [
        "entryStatus", "visualAccess", "auralAccess", "participationAccess",
        "entryDoesNotRecoverSensoryAccess", "canonicalSensoryAccessCoordinateDemand",
        "skilledContributionDoesNotImplyFreedom",
        "canonicalColonialTheatreSensoryAccessBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseEvidenceGraphExact.agda": [
        "SourceGenre", "SourceProductionContext", "sourceContext",
        "ManifestationContextReceipt", "julienSaleNoticeContextReceipt",
        "minetteWillContextReceipt", "liseAnnouncementContextReceipt",
        "minetteSalaryAnchor", "liseEventAnchor", "julienContributionBurdenAnchor",
        "portAuPrinceSeatingAnchor", "july1790ContestationAnchor",
        "graphReachabilityDoesNotCreateHistoricalIdentity",
        "coerciveAdvertisementDoesNotBecomeNeutralBiography",
        "sourceSilenceDoesNotCollapseAcrossGenres",
        "canonicalPowersEvidenceGraphBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseMobilityRegimeTransitionExact.agda": [
        "MobilityCoordinate", "RegimeCoordinate", "minetteMobilityCoordinate",
        "liseMobilityCoordinate", "carrierContinuityDoesNotRecoverRegimeContinuity",
        "repertoireContinuityDoesNotRecoverAccessContinuity",
        "canonicalPowersMobilityRegimeBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseResearchThroughPerformanceExact.agda": [
        "portAuPrinceSightlineProbe", "mitigatedAudibilityProbe",
        "backstageInformationFlowProbe", "powersPerformanceProbeDesign",
        "reconstructionDoesNotCreateHistoricalOccurrence",
        "probeAffordanceDoesNotCreateHistoricalFact",
        "canonicalPowersResearchThroughPerformanceBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseEmpiricalRoadmapExact.agda": [
        "phaseStatus", "statusOfDeliverable", "sourceAcquisitionPromotionGate",
        "empiricalFrontierGenealogy", "nextPriorityReference",
        "canonicalPowersEmpiricalRoadmapBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseEmpiricalPhase3Validation.agda": [
        "_methodology-boundary-paid", "_archive-modality-boundary-paid",
        "_five-axis-routing-paid", "_selective-reopening-paid",
        "_discriminator-boundary-paid", "_sensory-access-gap-paid",
        "_evidence-graph-boundary-paid", "_mobility-regime-boundary-paid",
        "_performance-probe-boundary-paid", "_source-acquisition-promotion-boundary-paid",
        "_location-inspection-gap-paid", "_frontier-genealogy-boundary-paid",
        "_compensation-frontier-genealogy-paid", "_roadmap-boundary-paid", "roadmapBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseSynthesisExact.agda": [
        "methodologySourceBoundary", "archiveModalityBoundary",
        "investigationRoutingBoundary", "historicalDiscriminatorBoundary",
        "sensoryAccessBoundary", "evidenceGraphBoundary",
        "mobilityRegimeBoundary", "researchThroughPerformanceBoundary",
        "sourceAcquisitionPromotionBoundary", "frontierGenealogyBoundary",
        "empiricalRoadmapBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseValidation.agda": [
        "PowersPlantationParadiseEmpiricalPhase3Validation",
        "_phase3-validation-reachable", "_roadmap-boundary-paid",
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

if errors:
    raise SystemExit("\n".join(errors))

print("Plantation to Paradise empirical phase-3 static contract: OK")
