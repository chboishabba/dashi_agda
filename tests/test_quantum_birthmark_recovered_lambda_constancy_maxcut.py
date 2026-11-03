from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_recovered_lambda_constancy_boundary_uses_same_field():
    p = text("DASHI/Quantum/QuantumBirthmarkJacobsonRecoveredLambdaConstancyBoundaryExact.agda")
    assert "recoveredLambdaSameObjectConstancySourceWritten" in p
    assert "separateLambdaIdentityWeldNoLongerRequired" in p
    assert "physicalBianchiToFDerivZeroStillRequired" in p
    assert "physicalStressConservationStillRequired" in p
    assert "physicalDomainChoiceStillRequired" in p


def test_rollup_registers_recovered_lambda_constancy_boundary():
    p = text("DASHI/Quantum/Everything.agda")
    assert "import DASHI.Quantum.QuantumBirthmarkJacobsonRecoveredLambdaConstancyBoundaryExact" in p
