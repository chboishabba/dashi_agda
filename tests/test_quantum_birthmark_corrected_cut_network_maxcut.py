from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_corrected_cut_network_boundary_records_exact_paid_layer():
    p = text("DASHI/Quantum/QuantumBirthmarkCorrectedCutNetworkBoundaryExact.agda")
    assert "correctedReplacementNetworkOwned" in p
    assert "correctedMinimalCutIdentificationOwned" in p
    assert "correctedNetworkSameObjectRTClosed" in p
    assert "upstreamReplacementOrEquivalenceStillRequired" in p
    assert "physicalAdSCFTStillRequired" in p


def test_quantum_rollup_registers_corrected_cut_network_boundary():
    p = text("DASHI/Quantum/Everything.agda")
    assert "import DASHI.Quantum.QuantumBirthmarkCorrectedCutNetworkBoundaryExact" in p
