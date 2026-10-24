from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_fibrewise_frame_boundary_records_pointwise_field_assembly():
    p = text("DASHI/Quantum/QuantumBirthmarkJacobsonFibrewiseFrameBoundaryExact.agda")
    assert "fibrewisePointwiseAssemblySourceWritten" in p
    assert "physicalFrameFieldConstructionStillRequired" in p
    assert "recoveredPhiSmoothnessStillRequired" in p
    assert "recoveredPhiDifferentiabilityStillRequired" in p
    assert "globalFrameTrivializationNotRequired" in p


def test_quantum_rollup_registers_fibrewise_frame_boundary():
    p = text("DASHI/Quantum/Everything.agda")
    assert "import DASHI.Quantum.QuantumBirthmarkJacobsonFibrewiseFrameBoundaryExact" in p
