from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_history_dark_energy_round2_owners_and_terminal():
    checks = {
        "DASHI/Quantum/QuantumBirthmarkHistoryCommonActionVariationExact.agda": [
            "finiteHistoryActionGenerationOwned",
            "commonMetricVariationStressCompilerOwned",
            "historyCommonActionCompilesStressWeld",
        ],
        "DASHI/Quantum/QuantumBirthmarkWeightedCommonActionExact.agda": [
            "BirthmarkWeightedCommonAction",
            "selectedBirthmarkHistoryActionIsLiteralAccumulation",
            "birthmarkSelectedHistoryToCommonActionCompilerOwned",
        ],
        "DASHI/Quantum/QuantumBirthmarkEq223SignLeafExact.agda": [
            "PreferredEq223LiteralSignLeaf",
            "sourceNativeVacuumCoefficientPositivityStillRequired",
            "sourceNativeERBNonnegativityStillRequired",
        ],
        "DASHI/Quantum/QuantumBirthmarkDarkEnergyCalibrationExact.agda": [
            "observedOmegaLambdaCentral",
            "calibratedTrackingCrossProduct",
            "parameterFreeOmegaPredictionOwned",
        ],
        "DASHI/Quantum/QuantumBirthmarkFiniteWallBounceExact.agda": [
            "finiteWallCarrierConstructed",
            "contractionToExpansionTurnaroundConstructed",
            "continuumFriedmannBounceSolutionConstructed",
        ],
        "DASHI/Quantum/QuantumBirthmarkDeSitterCoreLocalRegularityExact.agda": [
            "coreCenterLapse",
            "coreCenterFirstDerivative",
            "globalGeodesicCompletenessDerived",
        ],
        "DASHI/Quantum/QuantumBirthmarkLaboratoryBackreactionProtocolExact.agda": [
            "MatchedStressHistoryProtocol",
            "laboratoryProtocolCarrierOwned",
            "nonzeroDifferentialSignalPredictedByCurrentTheory",
        ],
        "DASHI/Quantum/QuantumBirthmarkFiniteHistoryTwoVacuumBenchmarkExact.agda": [
            "sameInitialStateDifferentHistoryActionReused",
            "finiteHistoryCanSelectDifferentVacuumPhase",
            "classifierDerivedFromQuantumBirthmarkDynamics",
        ],
        "DASHI/Quantum/QuantumBirthmarkVacuumEnergyDiscrepancyBoundaryExact.agda": [
            "massDensityExponentGapIs123",
            "quotedOneHundredTwentyOrdersIsConventionDependent",
            "vacuumEnergyProblemSolvedByCurrentHistoryModel",
        ],
    }
    for rel, tokens in checks.items():
        text = (ROOT / rel).read_text()
        for token in tokens:
            assert token in text

    terminal = (ROOT / "DASHI/Quantum/QuantumBirthmarkHistoryDarkEnergyTerminalMaxCutExact.agda").read_text()
    for token in [
        "eq223SignReducedToTwoLiteralLeaves",
        "observationalFractionCalibrationOwned",
        "finiteHistoryActionGenerationOwned",
        "finiteWallCarrierOwned",
        "finiteBounceKinematicsOwned",
        "laboratoryProtocolCarrierOwned",
        "RemainingHistoryDarkEnergyProducers",
        "sourceNativeVacuumCoefficientPositivity",
        "sourceNativeERBNonnegativity",
        "parameterFreeOmegaPrediction",
        "globalRegularBlackHoleExtensionAndGeodesicCompleteness",
        "sourcedContinuumFriedmannBounce",
    ]:
        assert token in terminal
