#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

EXPECTED = {
    "DASHI/Culture/PowersPlantationParadiseMethodologySourceAtlasExact.agda": [
        "prest2023PublicTheatreSource", "prest2023MethodologySource",
        "prest2024ResponseSource", "row2024ReviewSource", "sabee2024ReviewSource",
        "freedomOnTheMoveSource", "canonicalPowersMethodologySourceBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseInvestigationParetoExact.agda": [
        "primaryCorpusCandidate", "actorDistributionCandidate",
        "compensationSettlementCandidate", "seatingRuleCandidate",
        "causalIdentificationCandidate", "canonicalITIRBoundary",
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
        "minetteSalaryAnchor", "liseEventAnchor", "julienContributionBurdenAnchor",
        "portAuPrinceSeatingAnchor", "july1790ContestationAnchor",
        "graphReachabilityDoesNotCreateHistoricalIdentity",
        "coerciveAdvertisementDoesNotBecomeNeutralBiography",
        "canonicalPowersEvidenceGraphBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseResearchThroughPerformanceExact.agda": [
        "portAuPrinceSightlineProbe", "mitigatedAudibilityProbe",
        "backstageInformationFlowProbe", "powersPerformanceProbeDesign",
        "reconstructionDoesNotCreateHistoricalOccurrence",
        "probeAffordanceDoesNotCreateHistoricalFact",
        "canonicalPowersResearchThroughPerformanceBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseEmpiricalRoadmapExact.agda": [
        "phaseStatus", "statusOfDeliverable", "nextPriorityReference",
        "canonicalPowersEmpiricalRoadmapBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseEmpiricalPhase3Validation.agda": [
        "_methodology-boundary-paid", "_five-axis-routing-paid",
        "_discriminator-boundary-paid", "_sensory-access-gap-paid",
        "_evidence-graph-boundary-paid", "_performance-probe-boundary-paid",
        "_roadmap-boundary-paid", "roadmapBoundary",
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
