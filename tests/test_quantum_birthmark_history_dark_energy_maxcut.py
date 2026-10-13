from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_history_sector_dark_energy_maxcut_registered():
    owners = {
        "history": ROOT / "DASHI/Quantum/QuantumBirthmarkHistorySectorDarkEnergyExact.agda",
        "regular": ROOT / "DASHI/Quantum/QuantumBirthmarkRegularCoreBounceBoundaryExact.agda",
        "obs": ROOT / "DASHI/Quantum/QuantumBirthmarkCosmologyDiscriminatorExact.agda",
        "terminal": ROOT / "DASHI/Quantum/QuantumBirthmarkHistoryDarkEnergyTerminalMaxCutExact.agda",
    }
    for path in owners.values():
        assert path.exists()

    history = owners["history"].read_text()
    for token in [
        "HistorySectorEffectiveActionHypothesis",
        "birthmarkPersistenceNotEqualDarkEnergy",
        "metricVariationIsGravitySourceRoute",
        "landauerConverseIsInterpretiveNotTheorem",
        "uvVacuumCancellationNotClaimed",
        "horizonSuppressionRequiresDerivation",
        "coincidenceScalingRequiresDerivation",
    ]:
        assert token in history

    regular = owners["regular"].read_text()
    for token in [
        "deSitterCoreJunctionReused",
        "decRepulsiveExteriorReused",
        "nambuGotoRepulsiveBubbleReused",
        "regularBlackHoleNotYetDerived",
        "geodesicCompletenessStillRequired",
        "cosmologicalBounceNotYetDerived",
    ]:
        assert token in regular

    obs = owners["obs"].read_text()
    for token in [
        "evolvingEquationOfStateDiscriminator",
        "structureHistoryCorrelationDiscriminator",
        "laboratoryResidualBackreactionDiscriminator",
        "DESIDR2MixedEvidenceRecorded",
        "RomanLaunched20260830Recorded",
        "positiveSignalDoesNotUniquelyIdentifyHistorySector",
    ]:
        assert token in obs

    terminal = owners["terminal"].read_text()
    for token in [
        "historySectorEffectiveActionLaneOwned",
        "positiveGRepulsiveGeometryLaneOwned",
        "regularCoreCandidateLaneOwned",
        "cosmologyDiscriminatorLaneOwned",
        "cosmologicalConstantProblemSolvedIsFalse",
        "coincidenceProblemSolvedIsFalse",
        "singularityResolutionSolvedIsFalse",
        "historyDarkEnergySteelmanCrossPollinated",
    ]:
        assert token in terminal

    rollup = (ROOT / "DASHI/Quantum/Everything.agda").read_text()
    for name in [
        "QuantumBirthmarkHistorySectorDarkEnergyExact",
        "QuantumBirthmarkRegularCoreBounceBoundaryExact",
        "QuantumBirthmarkCosmologyDiscriminatorExact",
        "QuantumBirthmarkHistoryDarkEnergyTerminalMaxCutExact",
    ]:
        assert name in rollup
