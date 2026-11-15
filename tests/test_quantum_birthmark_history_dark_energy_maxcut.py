from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_history_sector_dark_energy_maxcut_registered():
    owners = {
        "history": ROOT / "DASHI/Quantum/QuantumBirthmarkHistorySectorDarkEnergyExact.agda",
        "horizon": ROOT / "DASHI/Quantum/QuantumBirthmarkHistoryHorizonScalingExact.agda",
        "potential": ROOT / "DASHI/Quantum/QuantumBirthmarkHistoryOrderParameterPotentialExact.agda",
        "phase": ROOT / "DASHI/Quantum/QuantumBirthmarkTwoPhaseHistoryModelExact.agda",
        "repulsive": ROOT / "DASHI/Quantum/QuantumBirthmarkHistoryRepulsiveGeometryInstantiationExact.agda",
        "ray": ROOT / "DASHI/Quantum/QuantumBirthmarkRaychaudhuriEnergyConditionFirewallExact.agda",
        "cpl": ROOT / "DASHI/Quantum/QuantumBirthmarkDarkEnergyCPLExact.agda",
        "atlas": ROOT / "DASHI/Quantum/QuantumBirthmarkDarkEnergySourceAtlasExact.agda",
        "regular": ROOT / "DASHI/Quantum/QuantumBirthmarkRegularCoreBounceBoundaryExact.agda",
        "obs": ROOT / "DASHI/Quantum/QuantumBirthmarkCosmologyDiscriminatorExact.agda",
        "terminal": ROOT / "DASHI/Quantum/QuantumBirthmarkHistoryDarkEnergyTerminalMaxCutExact.agda",
        "d1": ROOT / "DASHI/Physics/Foundations/CMP119D1StandardDifferentialAuthorityExact.agda",
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

    horizon = owners["horizon"].read_text()
    for token in [
        "horizonTrackingCrossProduct",
        "wFromScalingExponent",
        "vacuumWActiveStressFactor",
        "coincidenceMechanismModelledNotSolved",
    ]:
        assert token in horizon

    potential = owners["potential"].read_text()
    for token in [
        "historyVacuumPotential",
        "historyInteriorVacuum",
        "historyExteriorVacuum",
        "historyVacuumRatioInvariant",
        "finiteThreeSiteWallCarrierConstructed",
    ]:
        assert token in potential

    phase = owners["phase"].read_text()
    for token in [
        "HistoryPhase",
        "historyOrderParameter",
        "lowHistoryEnergy",
        "highHistoryEnergy",
        "microscopicPhaseSelectionStillRequired",
    ]:
        assert token in phase

    repulsive = owners["repulsive"].read_text()
    for token in [
        "historyDECRepulsiveExterior",
        "historyNambuGotoRepulsiveBubble",
        "twoVacuumDECAmplitudeModelAlreadyConstructed",
        "sourceNativeCMP119PotentialCouplingStillRequired",
    ]:
        assert token in repulsive

    ray = owners["ray"].read_text()
    for token in [
        "metricTermInvisibleToNullContractionReused",
        "secViolationIsTheRelevantVacuumAccelerationCondition",
        "pureLambdaGenericallyMakesNullRicciNegative",
        "nullRaychaudhuriDefocusingClaimRequiredForFLRWAcceleration",
    ]:
        assert token in ray

    cpl = owners["cpl"].read_text()
    for token in [
        "cplW",
        "lcdmIsConstantMinusOne",
        "presentEpochW",
        "nonzeroWaUniquelyIdentifiesHistorySector",
    ]:
        assert token in cpl

    atlas = owners["atlas"].read_text()
    for token in [
        "landauer1961",
        "birthmarkPRX2026",
        "desiDR2LyAlpha2026",
        "euclid2026",
        "roman2026",
        "noSourceAboveDirectlyEstablishesHistoryDarkEnergy",
    ]:
        assert token in atlas

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

    d1 = owners["d1"].read_text()
    for token in [
        "CMP119D1StandardDifferentialAuthority",
        "compileCorrectedD1Semantics",
        "currentBC2SourceRecordAloneProvesD1Linearity",
        "minimalD1AuthorityCutOwned",
    ]:
        assert token in d1

    terminal = owners["terminal"].read_text()
    for token in [
        "historySectorEffectiveActionLaneOwned",
        "positiveGRepulsiveGeometryLaneOwned",
        "regularCoreCandidateLaneOwned",
        "cosmologyDiscriminatorLaneOwned",
        "hubbleSquaredTrackingModelOwned",
        "historyScaledTwoVacuumPotentialOwned",
        "twoPhaseHistoryOrderParameterOwned",
        "repulsiveGeometryInstantiationOwned",
        "cplDiscriminatorCarrierOwned",
        "raychaudhuriEnergyConditionFirewallOwned",
        "correctedD1MinimalAuthorityCutOwned",
        "cosmologicalConstantProblemSolvedIsFalse",
        "coincidenceProblemSolvedIsFalse",
        "singularityResolutionSolvedIsFalse",
        "historyDarkEnergySteelmanCrossPollinated",
    ]:
        assert token in terminal

    rollup = (ROOT / "DASHI/Quantum/Everything.agda").read_text()
    for name in [
        "QuantumBirthmarkHistorySectorDarkEnergyExact",
        "QuantumBirthmarkHistoryHorizonScalingExact",
        "QuantumBirthmarkHistoryOrderParameterPotentialExact",
        "QuantumBirthmarkTwoPhaseHistoryModelExact",
        "QuantumBirthmarkHistoryRepulsiveGeometryInstantiationExact",
        "QuantumBirthmarkRaychaudhuriEnergyConditionFirewallExact",
        "QuantumBirthmarkDarkEnergyCPLExact",
        "QuantumBirthmarkDarkEnergySourceAtlasExact",
        "QuantumBirthmarkRegularCoreBounceBoundaryExact",
        "QuantumBirthmarkCosmologyDiscriminatorExact",
        "QuantumBirthmarkHistoryDarkEnergyTerminalMaxCutExact",
    ]:
        assert name in rollup
