from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_raychaudhuri_equilibrium_boundary_reuses_existing_authority():
    p = text("DASHI/Quantum/QuantumBirthmarkJacobsonRaychaudhuriEquilibriumBoundaryExact.agda")
    assert "NullRaychaudhuriSachsFocusingExact" in p
    assert "equilibriumRaychaudhuriAlgebraSourceWritten" in p
    assert "physicalNullCongruenceEquationStillRequired" in p
    assert "localEquilibriumIdentificationStillRequired" in p
    assert "hypersurfaceOrthogonalityStillRequired" in p
    assert "higherOrderControlStillRequired" in p


def test_quantum_rollup_registers_raychaudhuri_equilibrium_boundary():
    p = text("DASHI/Quantum/Everything.agda")
    assert "import DASHI.Quantum.QuantumBirthmarkJacobsonRaychaudhuriEquilibriumBoundaryExact" in p
