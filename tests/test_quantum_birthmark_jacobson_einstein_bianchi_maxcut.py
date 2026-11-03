from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_einstein_bianchi_boundary_tracks_native_lean_producers_and_repo_receipts():
    p = text("DASHI/Quantum/QuantumBirthmarkJacobsonEinsteinTensorBianchiBoundaryExact.agda")
    assert "ContractedBianchiMatterClosure" in p
    assert "flat31JacobsonEinsteinCompilerSourceWrittenInLean" in p
    assert "einsteinTensorPointwiseAlgebraSourceWrittenInLean" in p
    assert "bianchiLambdaGradientCompilerSourceWrittenInLean" in p
    assert "mathlibZeroDerivativeConstancyOwned" in p
    assert "physicalLambdaFDerivZeroStillRequired" in p
    assert "sameObjectStressEnergyAuthorityStillRequired" in p


def test_terminal_cutset_marks_einstein_bianchi_algebra_paid():
    p = text("DASHI/Quantum/QuantumBirthmarkHolographyGravityTerminalCutsetExact.agda")
    assert "flat31JacobsonEinsteinCompilerSourceWrittenInLean" in p
    assert "einsteinTensorPointwiseAlgebraSourceWrittenInLean" in p
    assert "bianchiLambdaGradientCompilerSourceWrittenInLean" in p
    assert "mathlibZeroDerivativeConstancyOwned" in p


def test_quantum_rollup_registers_einstein_bianchi_boundary():
    p = text("DASHI/Quantum/Everything.agda")
    assert "import DASHI.Quantum.QuantumBirthmarkJacobsonEinsteinTensorBianchiBoundaryExact" in p
