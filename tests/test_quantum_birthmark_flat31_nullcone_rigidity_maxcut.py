from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_flat31_rigidity_boundary_tracks_native_lean_producer():
    p = text("DASHI/Quantum/QuantumBirthmarkJacobsonFlat31RigidityBoundaryExact.agda")
    assert "FlatLorentzianModel" in p
    assert "finiteFlat31RigiditySourceWrittenInLean" in p
    assert "flat31RigidityKernelReceiptStillRequired" in p
    assert "lorentzFrameTransportCompilerSourceWrittenInLean" in p
    assert "physicalTangentFrameIdentificationStillRequired" in p
    assert "frameSmoothnessOrGlobalAssemblyStillRequired" in p


def test_terminal_cutset_splits_rigidity_leaf_after_flat31_producer():
    p = text("DASHI/Quantum/QuantumBirthmarkHolographyGravityTerminalCutsetExact.agda")
    assert "flat31RigidityKernelReceiptStillRequired" in p
    assert "lorentzFrameTransportCompilerSourceWrittenInLean" in p
    assert "physicalTangentFrameIdentificationStillRequired" in p
    assert "frameSmoothnessOrGlobalAssemblyStillRequired" in p


def test_quantum_rollup_registers_flat31_rigidity_boundary():
    p = text("DASHI/Quantum/Everything.agda")
    assert "import DASHI.Quantum.QuantumBirthmarkJacobsonFlat31RigidityBoundaryExact" in p
