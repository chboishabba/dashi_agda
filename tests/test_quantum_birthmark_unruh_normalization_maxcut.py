from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_unruh_normalization_boundary_pins_bw_sources_and_scalar_payment():
    p = text("DASHI/Quantum/QuantumBirthmarkJacobsonUnruhNormalizationBoundaryExact.agda")
    assert "BisognanoWichmann1975" in p
    assert "BisognanoWichmann1976" in p
    assert "10.1063/1.522605" in p
    assert "10.1063/1.522898" in p
    assert "boostKMSNormalizationSourceWritten" in p
    assert "physicalBisognanoWichmannStillRequired" in p
    assert "accelerationProperTimeIdentificationStillRequired" in p
    assert "modularKMSAnalyticStripStillRequired" in p


def test_terminal_extension_distinguishes_unruh_scalar_from_bw_qft_payment():
    p = text("DASHI/Quantum/QuantumBirthmarkHolographyGravityUnruhTerminalExtensionExact.agda")
    assert "unruhScalarNormalizationOwned" in p
    assert "physicalBisognanoWichmannStillRequired" in p
    assert "priorTerminalPhysicalCutsetStillAvailable" in p


def test_quantum_rollup_registers_unruh_normalization_boundary_and_terminal_extension():
    p = text("DASHI/Quantum/Everything.agda")
    assert "import DASHI.Quantum.QuantumBirthmarkJacobsonUnruhNormalizationBoundaryExact" in p
    assert "import DASHI.Quantum.QuantumBirthmarkHolographyGravityUnruhTerminalExtensionExact" in p
