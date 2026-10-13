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
        "declaredBenchmarkResidualEmpty",
    ]:
        assert token in owner
    assert "QuantumBirthmarkTerminalConcreteInstantiationExact" in rollup
