from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_entropy_density_to_expansion_maxcut_registered():
    owner = (ROOT / "DASHI/Quantum/QuantumBirthmarkEntropyDensityExpansionMaxCutExact.agda").read_text()
    rollup = (ROOT / "DASHI/Quantum/Everything.agda").read_text()
    for token in [
        "ResidualEffectiveDensityInstantiation",
        "selectedResidualSectorMapsToGeneratedDensity",
        "residualTraceReadoutMatchesContinuumTrace",
        "residualTraceNegativeForcesPositiveMatterAcceleration",
        "densityMetricVariationStressRouteReused",
        "vacuumActiveStressExpansionRouteReused",
        "birthmarkPersistenceSuppliesResidualSectorSemantics",
        "residualDensityIsNotIdentifiedWithThermodynamicEntropy",
        "negativeGravityConstantNotUsed",
        "negativeInertialMassNotUsed",
        "formalCrossLaneCompositionClosed",
    ]:
        assert token in owner
    assert "BalabanUnifiedGeneratedActionDensityRound132Exact" in owner
    assert "CMP119CosmologyRealTraceToExpansionMaxCutExact" in owner
    assert "QuantumBirthmarkEntropyDensityExpansionMaxCutExact" in rollup
