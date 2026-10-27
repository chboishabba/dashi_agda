from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_jacobson_coupling_boundary_tracks_native_lean_algebra():
    p = text("DASHI/Quantum/QuantumBirthmarkJacobsonCouplingNormalizationBoundaryExact.agda")
    assert "jacobsonCouplingAlgebraSourceWrittenInLean" in p
    assert "eightPiGSpecializationSourceWrittenInLean" in p
    assert "clausiusNullAlgebraSourceWrittenInLean" in p
    assert "unruhNormalizationPhysicalReceiptStillRequired" in p
    assert "entropyAreaPhysicalReceiptStillRequired" in p
    assert "geometricHeatFluxReceiptStillRequired" in p
    assert "raychaudhuriSameCarrierStillRequired" in p


def test_terminal_cutset_marks_coupling_algebra_paid_but_physics_open():
    p = text("DASHI/Quantum/QuantumBirthmarkHolographyGravityTerminalCutsetExact.agda")
    assert "jacobsonCouplingAlgebraSourceWrittenInLean" in p
    assert "eightPiGSpecializationSourceWrittenInLean" in p
    assert "clausiusNullAlgebraSourceWrittenInLean" in p


def test_quantum_rollup_registers_coupling_boundary():
    p = text("DASHI/Quantum/Everything.agda")
    assert "import DASHI.Quantum.QuantumBirthmarkJacobsonCouplingNormalizationBoundaryExact" in p
