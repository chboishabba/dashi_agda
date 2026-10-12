from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_contract_spectrum_owner_closes_full_state_entropy_gap_and_separates_subsystem_gap():
    p = text("DASHI/Quantum/QuantumBirthmarkHolographicContractEntropyExact.agda")
    assert "holographicContractIsUniformDiagonal" in p
    assert "uniformEigenvalueMultiplicity" in p
    assert "uniformTraceNormalisation" in p
    assert "fullContractVonNeumannEntropyIsNLogTwo" in p
    assert "fullStateEntropyMatchesTreeEntropyAtFullDepth" in p
    assert "factorizedSubsystemRTClosed" in p
    assert "upstreamZModSubsystemFactorizationStillRequired" in p
    assert "subsystemReducedDensityMatrixStillRequired" in p
    assert "fullContractDoesNotByItselfProveDepthKSubsystemEntropy" in p


def test_same_object_weld_consumes_contract_entropy_owner():
    p = text("DASHI/Quantum/QuantumBirthmarkHolographicSameObjectWeldExact.agda")
    assert "QuantumBirthmarkHolographicContractEntropyExact" in p
    assert "fullStateDensityMatrixEntropyWeldClosed" in p
    assert "factorizedSubsystemEntropyWeldClosed" in p
    assert "upstreamZModSubsystemFactorizationStillRequired" in p
    assert "subsystemReducedDensityMatrixWeldStillRequired" in p


def test_quantum_rollup_registers_contract_entropy_owner():
    p = text("DASHI/Quantum/Everything.agda")
    assert "import DASHI.Quantum.QuantumBirthmarkHolographicContractEntropyExact" in p
