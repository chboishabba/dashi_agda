from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_horizon_flux_area_boundary_records_exact_reductions_and_source():
    p = text("DASHI/Quantum/QuantumBirthmarkJacobsonHorizonFluxAreaBoundaryExact.agda")
    assert "10.1103/PhysRevLett.75.1260" in p
    assert "horizonFluxReductionSourceWritten" in p
    assert "linearizedAreaReductionSourceWritten" in p
    assert "physicalBoostKillingFieldStillRequired" in p
    assert "physicalHorizonMeasureStillRequired" in p
    assert "continuumHigherOrderControlStillRequired" in p


def test_rollup_registers_horizon_flux_area_boundary():
    p = text("DASHI/Quantum/Everything.agda")
    assert "import DASHI.Quantum.QuantumBirthmarkJacobsonHorizonFluxAreaBoundaryExact" in p
