from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_entropy_density_has_surface_area_normalisation():
    p = text("DASHI/Physics/Foundations/EntropyDensityExact.agda")
    assert "surfaceArea" in p
    assert "entropyPerArea" in p
    assert "entropyPerAreaIsNotEntropyPerVolume" in p


def test_jacobson_maxcut_reuses_existing_qft_gr_owners():
    p = text("DASHI/Quantum/QuantumBirthmarkJacobsonLocalHorizonMaxCutExact.agda")
    assert "NullRaychaudhuriSachsFocusingExact" in p
    assert "ModularTheoryReceiptSurface" in p
    assert "EinsteinTensor" in p
    assert "StressEnergyCompatibility" in p
    assert "ContinuumEinsteinMatterSolutionBoundary" in p
    assert "EinsteinEquationBidiResidualExact" in p
    assert "surfaceEntropyDensity" in p
    assert "localRindlerHorizon" in p
    assert "unruhTemperatureNormalization" in p
    assert "clausiusRelation" in p
    assert "raychaudhuriAreaVariation" in p
    assert "heatFluxStressEnergy" in p
    assert "allNullDirections" in p
    assert "einsteinEquationOfStateTarget" in p


def test_jacobson_reuses_finite_sourced_law_but_not_as_continuum_derivation():
    p = text("DASHI/Quantum/QuantumBirthmarkJacobsonLocalHorizonMaxCutExact.agda")
    assert "finiteSourcedEinsteinLawAlreadyOwned" in p
    assert "continuumEinsteinMatterSolutionSchemaOwned" in p
    assert "finiteSourcedEinsteinDoesNotPayContinuumJacobson" in p
    assert "continuumSolutionSchemaDoesNotSupplyJacobsonDerivation" in p


def test_jacobson_authority_boundary_is_fail_closed():
    p = text("DASHI/Quantum/QuantumBirthmarkJacobsonLocalHorizonMaxCutExact.agda")
    assert "unruhStillTargetNotLocalTheorem" in p
    assert "raychaudhuriStillAuthorityTarget" in p
    assert "sourcedStressEnergyStillBlocked" in p
    assert "localVacuumEinsteinSurfaceDoesNotPaySourcedJacobson" in p
    assert "entropyPerAreaIsNotEntropyPerVolume" in p
    assert "birthmarkResidualIsNotHorizonEntropy" in p


def test_quantum_rollup_registers_jacobson_maxcut():
    p = text("DASHI/Quantum/Everything.agda")
    assert "import DASHI.Quantum.QuantumBirthmarkJacobsonLocalHorizonMaxCutExact" in p
