from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_terminal_physical_compiler_boundary():
    p = text("DASHI/Quantum/QuantumBirthmarkJacobsonPhysicalTerminalCompilerBoundaryExact.agda")
    assert "terminalConditionalEinsteinCompilerSourceWritten" in p
    assert "noFurtherInternalJacobsonAlgebraDebt" in p
    assert "physicalSameObjectConstructionStillRequired" in p
    assert "constantLambdaEinsteinEquationOnSameDomain" in p


def test_rollup_registers_terminal_physical_compiler_boundary():
    p = text("DASHI/Quantum/Everything.agda")
    assert "import DASHI.Quantum.QuantumBirthmarkJacobsonPhysicalTerminalCompilerBoundaryExact" in p
