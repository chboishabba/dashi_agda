from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_continuum_adapter_reuses_existing_solution_schema():
    p = text("DASHI/Quantum/QuantumBirthmarkJacobsonContinuumSolutionAdapterExact.agda")
    assert "ContinuumEinsteinMatterSolutionBoundary" in p
    assert "continuumSolutionSchemaReused" in p
    assert "noSecondContinuumSolutionFormalismRequired" in p
    assert "physicalInstantiationStillRequired" in p


def test_rollup_registers_continuum_adapter():
    p = text("DASHI/Quantum/Everything.agda")
    assert "import DASHI.Quantum.QuantumBirthmarkJacobsonContinuumSolutionAdapterExact" in p
