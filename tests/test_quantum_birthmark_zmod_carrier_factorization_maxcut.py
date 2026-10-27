from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_zmod_carrier_factorization_boundary_closes_only_carrier_layer():
    p = text("DASHI/Quantum/QuantumBirthmarkHolographicZModCarrierFactorizationBoundaryExact.agda")
    assert "upstreamZModCarrierFactorizationSourceWritten" in p
    assert "carrierBijectionNoLongerRequired" in p
    assert "depthKSubtreeSemanticIdentificationStillRequired" in p
    assert "minimalCutSemanticIdentificationStillRequired" in p
    assert "tensorNetworkStateIdentificationStillRequired" in p


def test_rollup_registers_zmod_carrier_factorization_boundary():
    p = text("DASHI/Quantum/Everything.agda")
    assert "import DASHI.Quantum.QuantumBirthmarkHolographicZModCarrierFactorizationBoundaryExact" in p
