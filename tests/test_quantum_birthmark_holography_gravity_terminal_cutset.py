from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_terminal_cutset_reduces_live_frontier_to_paid_physical_welds():
    p = text("DASHI/Quantum/QuantumBirthmarkHolographyGravityTerminalCutsetExact.agda")
    assert "correctedFiniteRTEntropyClosed" in p
    assert "birthmarkResidualTransportCompilerOwned" in p
    assert "upstreamStateCarrierIdentification" in p
    assert "physicalBulkBoundaryDictionary" in p
    assert "birthmarkResidualTransport" in p
    assert "physicalBirthmarkBoundaryFactorizationStillRequired" in p
    assert "localHorizonSameObjectWeld" in p
    assert "unruhRindlerKernelTheorem" in p
    assert "clausiusEntropyAreaSameObjectReceipt" in p
    assert "nullRaychaudhuriContinuumKernelTheorem" in p
    assert "sameObjectMatterStressEnergyReceipt" in p
    assert "allNullDirectionsTensorRecovery" in p
    assert "einsteinEquationOfStateKernelDerivation" in p
    assert "continuumPhysicalSolutionAttachment" in p
    assert "jacobsonDifferentialGeometricDerivation" in p
    assert "empiricalValidation" in p


def test_terminal_cutset_blocks_unpaid_promotions():
    p = text("DASHI/Quantum/QuantumBirthmarkHolographyGravityTerminalCutsetExact.agda")
    assert "finiteRTDoesNotImplyPhysicalRT" in p
    assert "holographyDoesNotImplyJacobson" in p
    assert "birthmarkDoesNotImplyCurvature" in p
    assert "entropyDensityDoesNotImplyStressTensor" in p
    assert "observableTransportDoesNotImplyBulkReconstruction" in p


def test_rollup_registers_terminal_cutset():
    p = text("DASHI/Quantum/Everything.agda")
    assert "import DASHI.Quantum.QuantumBirthmarkHolographyGravityTerminalCutsetExact" in p
