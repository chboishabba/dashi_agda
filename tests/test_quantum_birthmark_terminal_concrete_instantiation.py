from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def test_terminal_concrete_instantiation_registered():
    owner = (ROOT / "DASHI/Quantum/QuantumBirthmarkTerminalConcreteInstantiationExact.agda").read_text()
    rollup = (ROOT / "DASHI/Quantum/Everything.agda").read_text()
    for token in [
        "correctedIndependentBellTreeInstantiated",
        "vacuumJacobsonBenchmarkInstantiated",
        "stadiumCalibrationConsumed",
        "siPlanckCalibrationRecorded",
        "codataNewtonCalibrationRecorded",
        "entropyDensityExpansionCompilerRegistered",
        "preferredResidualEq223AdapterRegistered",
        "positiveGAntigravityEndpointRegistered",
        "flrwExpansionEndpointRegistered",
        "preferredCMP119SignRouteRegistered",
        "declaredBenchmarkResidualEmpty",
    ]:
        assert token in owner
    assert "QuantumBirthmarkResidualEq223ExpansionExact" in owner
    assert "QuantumBirthmarkTerminalConcreteInstantiationExact" in rollup
