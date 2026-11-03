from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_local_frame_einstein_lambda_boundary_records_pointwise_equation():
    p = text("DASHI/Quantum/QuantumBirthmarkJacobsonLocalFrameEinsteinLambdaBoundaryExact.agda")
    assert "localFrameEinsteinLambdaCompilerSourceWritten" in p
    assert "pointwiseEinsteinEquationSourceWritten" in p
    assert "recoveredLambdaFieldSourceWritten" in p
    assert "bianchiStressConservationStillRequired" in p
    assert "recoveredLambdaRegularityStillRequired" in p


def test_rollup_registers_local_frame_einstein_lambda_boundary():
    p = text("DASHI/Quantum/Everything.agda")
    assert "import DASHI.Quantum.QuantumBirthmarkJacobsonLocalFrameEinsteinLambdaBoundaryExact" in p
