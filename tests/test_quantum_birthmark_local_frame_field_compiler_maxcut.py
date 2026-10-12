from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_local_frame_field_compiler_boundary_records_composed_equation_of_state():
    p = text("DASHI/Quantum/QuantumBirthmarkJacobsonLocalFrameFieldCompilerBoundaryExact.agda")
    assert "localFrameFieldCompilerSourceWritten" in p
    assert "pointIndexedPhiFieldSourceWritten" in p
    assert "physicalLocalLorentzFrameStillRequired" in p
    assert "physicalClausiusSameObjectStillRequired" in p
    assert "recoveredPhiRegularityStillRequired" in p


def test_rollup_registers_local_frame_field_compiler_boundary():
    p = text("DASHI/Quantum/Everything.agda")
    assert "import DASHI.Quantum.QuantumBirthmarkJacobsonLocalFrameFieldCompilerBoundaryExact" in p
