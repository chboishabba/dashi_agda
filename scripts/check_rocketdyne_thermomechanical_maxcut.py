#!/usr/bin/env python3
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
EXPECT = {
    "DASHI/Physics/Propulsion/Rocketdyne1974MaterialIdentityAndConstitutiveDataExact.agda": ["wc103IdentityPaid", "vh101CoatingPaid", "haynes25At2000F", "c103HistoricalCreepAnchor"],
    "DASHI/Physics/Propulsion/Rocketdyne1974TwoMaterialDiscriminatorExact.agda": ["sameModelRule", "haynesDamageObserved", "wc103FollowupSurvived", "currentDiscriminator"],
    "DASHI/Physics/Propulsion/Rocketdyne1974IdentifiabilityCutExact.agda": ["twoThicknessesSameLoad", "geometryFreeStressNotUnique"],
    "DASHI/Physics/Propulsion/Rocketdyne1974ThermalModelValidationExact.agda": ["test052ThermalValidation", "steadyStateTimeSeconds", "sourceValidatedThermalModelExists", "thermalModelDoesNotIdentifyNozzleStress"],
    "DASHI/Physics/Propulsion/Rocketdyne1974MaterialDependentThermalFalsifierExact.agda": ["sameReportedEquilibriumTemperature", "wc103LongerExposureSurvived", "materialBlindTemperatureOnlyModelRefuted", "materialIdentityIsNecessaryDiscriminator"],
    "DASHI/Physics/Propulsion/Rocketdyne1974TerminalPhysicalFrontierExact.agda": ["currentTerminalFrontier", "archiveGeometryExhaustedForUniqueStress", "sameModelCalibrationStillOpen", "empiricalMaterialDependencePaid", "contemporaryComparatorReceipt", "experimentalCoordinateReceipt", "qualificationFeedbackReceipt", "programmeChallengeReceipt", "siblingRCSComparisonReceipt", "operationalShuttleContextReceipt", "flightC103ManufacturingLessonReceipt", "operationalValveReliabilityReceipt", "hotSectionQualificationFrontierReceipt", "operationsReliabilityFrontierReceipt", "inspectionCapabilityReceipt", "modelCredibilityReceipt", "manufacturingProcessHistoryPaid", "inspectionHistoryPaid"],
    "DASHI/Physics/Propulsion/Rocketdyne1974LatestSourceComparisonNote.agda": ["nasa2026NiobiumComparator", "canonicalContemporaryComparatorBoundary", "contemporaryComparatorDoesNotPayHistoricalLaw"],
    "DASHI/Physics/Propulsion/Rocketdyne1974ExperimentalCoordinateRefinementExact.agda": ["rocketdyneExperimentDesign", "temperatureCollision", "materialSeparatesTemperatureCollision", "nextCoordinateAcquisitionFrontier", "manufacturingProcessCoordinateOpen"],
    "DASHI/Physics/Propulsion/Rocketdyne1974QualificationFeedbackWeldExact.agda": ["haynesAnomalyToRevisionCandidate", "wc103FollowupObservation", "formalApprovalStillUnpaid", "adaptiveQualificationBoundaryReceipt", "environmentalProtectionRecommendation", "siblingComparisonDoesNotProveReliability", "operationalValveReliabilityBoundary"],
    "DASHI/Physics/Propulsion/Rocketdyne1974ProgrammeChallengesAndRelatedWorkExact.agda": ["canonicalChallengeAtlas", "sandDustValveChallenge", "orificePluggingChallenge", "lowThrottleOscillationChallenge", "vikingOperatingEnvelopeLineage", "interegenTradeoffReceipt", "valveSerialFailurePair", "sandAbradedTeflonSealMechanism"],
    "DASHI/Physics/Propulsion/Rocketdyne1974SiblingRCSComparisonExact.agda": ["bellNAS912996Comparator", "sameShuttleRequirementDifferentCoolingArchitecture", "bellEnvironmentalCycleComparator", "siblingComparisonBoundary", "valveContractOriginPaid", "exactBellEngineValveAssignmentPaid"],
    "DASHI/Physics/Propulsion/Rocketdyne1974OperationalShuttleContextExact.agda": ["orbiterRCSChallengeSet", "operationalRCSArchitecture", "rocketdyneTechnologyNotFlightIdentity", "operationalContextBoundary", "operationalPrimarySupplierPaid", "marquardtR40AFlightIdentity"],
    "DASHI/Physics/Propulsion/Rocketdyne1974FlightC103ManufacturingLessonExact.agda": ["shuttleC103CrackingLesson", "manufacturingProcessIsIndependentCoordinate", "historicalCauseDoesNotTransferToRocketdyne", "nescDocumentationLesson"],
    "DASHI/Physics/Propulsion/Rocketdyne1974OperationalValveReliabilityLessonExact.agda": ["shuttleMetalNitrateValveLesson", "sharedValveReliabilityCoordinate", "differentFailureMechanismFromRocketdyneSand", "operationalValveReliabilityBoundary"],
    "DASHI/Physics/Propulsion/Rocketdyne1974HotSectionQualificationFrontierExact.agda": ["rocketdyneQualificationReverseFrontier", "processRouteObligation", "geometryRevisionObligation", "inspectionObligation", "lifeReliabilityObligation", "fullQualificationPaymentStillOpen"],
    "DASHI/Physics/Propulsion/Rocketdyne1974OperationsReliabilityFrontierExact.agda": ["rocketdyneOperationsReliabilityFrontier", "serviceabilityPopulationBoundary", "operationsObligations", "reliabilityObligations", "populationIdentityObligation", "maintenanceFindingsObligation"],
    "DASHI/Physics/Propulsion/Rocketdyne1974OperationsReliabilityFrontierValidation.agda": ["operationsFrontierExists", "serviceabilityOpen", "maintenanceObligationExists", "reliabilityObligationExists"],
    "DASHI/Physics/Propulsion/Rocketdyne1974ContemporaryQualificationPHMSourceAtlasExact.agda": ["nasaSTD6030", "nasaHDBK5026", "nasaSTD5023", "nasaSTD5012C", "nasaSTD5009C", "nasaSTD5019AChange4", "nasaSTD7009B", "nasaHDBK7009B", "raambo", "c103HeatTreatment2025", "lreHealthMonitoring2026", "contemporarySourceAtlasBoundary", "attributionFirewall"],
    "DASHI/Physics/Propulsion/Rocketdyne1974InspectionCapabilityPODExact.agda": ["canonicalInspectionCapabilityFrontier", "quantitativePODRequiredForFractureCriticalClaim", "inspectionPresenceDoesNotPayDetectionCapability", "historicalInspectionCapabilityUnpaid", "modernPODRequirementDoesNotApplyRetroactively"],
    "DASHI/Physics/Propulsion/Rocketdyne1974ModelCredibilityValidationExact.agda": ["test052CredibilityFrontier", "sourceReportedCorrelationPaid", "numericalValidationErrorUnpaid", "uncertaintyPropagationUnpaid", "offDesignPredictionUnpaid", "sameModelTwoRunValidationTarget", "genericModelBoundary"],
    "DASHI/Physics/Propulsion/Rocketdyne1974DigitalThreadExperimentParetoExact.agda": ["digitalThreadBoundary", "wallGaugeAndContour", "test052ThermalField", "fabricationTraveler", "inspectionNDEHistory", "constitutiveData", "maintenanceFRACAS", "populationLedger", "sourceSelectionRecords", "rocketdyneAcquisitionPortfolio", "rocketdyneDigitalThreadExperimentFrontier"],
    "DASHI/Physics/Propulsion/Rocketdyne1974DigitalThreadExperimentParetoValidation.agda": ["frontierExists", "paretoBundleExists", "digitalThreadBoundaryExists", "inspectionCapabilityFrontierExists", "modelCredibilityFrontierExists"],
    "DASHI/Physics/Materials/RocketdyneMaterialSurvivabilityCrossPollinationExact.agda": ["flightC103ManufacturingLesson", "manufacturingProcessCoordinateRequired"],
    "DASHI/Physics/Materials/FusionPropulsionMaterialSurvivabilityCrossPollinationExact.agda": ["rocketdyneQualificationReverseFrontier", "canonicalHotSectionQualificationBoundary", "fusionQualificationNeedsOwnSameObjectPayment", "rocketdyneDigitalThreadFrontier", "fusionMayReuseDigitalThreadGrammar", "rocketdyneAcquisitionScoresTransferToFusion", "rocketdyneInspectionCapabilityFrontier", "rocketdyneModelCredibilityFrontier", "fusionMayReuseInspectionCapabilityGrammar", "rocketdynePODTransfersToFusion", "fusionMayReuseModelCredibilityGrammar", "rocketdyneValidationResidualTransfersToFusion"],
}

def main() -> int:
    failures = []
    for rel, tokens in EXPECT.items():
        p = ROOT / rel
        if not p.exists():
            failures.append(f"missing file: {rel}")
            continue
        text = p.read_text(encoding="utf-8")
        for token in tokens:
            if token not in text:
                failures.append(f"{rel}: missing export {token}")
    if failures:
        print("Rocketdyne thermomechanical max-cut: FAIL")
        print("\n".join(failures))
        return 1
    print("Rocketdyne thermomechanical max-cut: PASS")
    return 0

if __name__ == "__main__":
    sys.exit(main())
