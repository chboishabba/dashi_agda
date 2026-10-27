from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_entropy_density_owner_exists_and_separates_normalisations():
    s = text("DASHI/Physics/Foundations/EntropyDensityExact.agda")
    assert "record EntropyDensitySurface" in s
    assert "entropyPerVolume" in s
    assert "entropyPerSite" in s
    assert "entropyProductionDensity" in s
    assert "residualInformationDensity" in s
    assert "thermodynamicEntropyDensityIsResidualInformationDensity" in s


def test_entropic_gravity_sources_are_attribution_safe():
    s = text("DASHI/Physics/Foundations/EntropicGravitySourceBoundaryExact.agda")
    assert "10.1103/PhysRevD.7.2333" in s
    assert "10.1103/PhysRevLett.75.1260" in s
    assert "10.1007/JHEP04(2011)029" in s
    assert "bekensteinHawkingAreaEntropyIsSemiclassicalInput" in s
    assert "jacobsonDerivesEinsteinEquationFromLocalHorizonThermodynamicAssumptions" in s
    assert "verlindeEntropicGravityIsHeuristicEmergentGravityProposal" in s
    assert "entropyDensityAloneImpliesEinsteinEquation" in s


def test_birthmark_bridge_keeps_high_entropy_distinct_from_erasure():
    s = text("DASHI/Quantum/QuantumBirthmarkEntropyDensityGravityBridgeExact.agda")
    assert "highCoarseEntropyDoesNotImplyResidualErasure" in s
    assert "birthmarkMemoryDoesNotByItselfSourceCurvature" in s
    assert "jacobsonBridgeRequiresHorizonHeatTemperatureEntropyAssumptions" in s
    assert "verlindeBridgeRequiresHolographicScreenAssumptions" in s
    assert "entropyDensityResidualInformationAndEntropyProductionRemainDistinct" in s


def test_quantum_rollup_registers_bridge():
    s = text("DASHI/Quantum/Everything.agda")
    assert "DASHI.Quantum.QuantumBirthmarkEntropyDensityGravityBridgeExact" in s
