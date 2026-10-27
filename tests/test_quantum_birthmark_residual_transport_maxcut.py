from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_birthmark_residual_transport_is_consumer_relative():
    p = text("DASHI/Quantum/QuantumBirthmarkHolographicResidualTransportExact.agda")
    assert "BirthmarkObservableTransport" in p
    assert "boundaryBirthmark" in p
    assert "transportLaw" in p
    assert "boundaryEqualityPreservesBirthmark" in p
    assert "consumerSufficiencyIsEnoughForBirthmarkObservable" in p


def test_transport_does_not_promote_full_bulk_reconstruction():
    p = text("DASHI/Quantum/QuantumBirthmarkHolographicResidualTransportExact.agda")
    assert "birthmarkTransportDoesNotRequireBulkInjectivity" in p
    assert "observableTransportDoesNotIdentifyEntropy" in p
    assert "observableTransportDoesNotIdentifyResidualInformationDensity" in p
    assert "physicalBoundaryFactorizationStillRequired" in p


def test_terminal_cutset_uses_compiler_not_vague_transport_gap():
    p = text("DASHI/Quantum/QuantumBirthmarkHolographyGravityTerminalCutsetExact.agda")
    assert "birthmarkResidualTransportCompilerOwned" in p
    assert "physicalBirthmarkBoundaryFactorizationStillRequired" in p


def test_quantum_rollup_registers_residual_transport_owner():
    p = text("DASHI/Quantum/Everything.agda")
    assert "import DASHI.Quantum.QuantumBirthmarkHolographicResidualTransportExact" in p
