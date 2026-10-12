from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_2026_relative_entropy_source_is_bounded_and_attributed():
    p = text("DASHI/Quantum/QuantumBirthmarkRelativeEntropyJacobsonSourceBridgeExact.agda")
    assert "DorauMuch2026" in p
    assert "10.1103/lmq8-nsty" in p
    assert "relativeEntropyEnergyFlux" in p
    assert "areaVariationAssumption" in p
    assert "coherentScalarExcitationScope" in p


def test_relative_entropy_lane_does_not_collapse_birthmark_or_rt_entropy():
    p = text("DASHI/Quantum/QuantumBirthmarkRelativeEntropyJacobsonSourceBridgeExact.agda")
    assert "relativeEntropyIsNotBirthmarkMemory" in p
    assert "relativeEntropyIsNotRyuTakayanagiEntropy" in p
    assert "paperDoesNotEstablishGeneralStateUniversality" in p
    assert "paperDoesNotEstablishNonperturbativeQuantumGravity" in p


def test_terminal_cutset_registers_relative_entropy_alternative_lane():
    p = text("DASHI/Quantum/QuantumBirthmarkHolographyGravityTerminalCutsetExact.agda")
    assert "relativeEntropyHorizonFluxAuthorityOwned" in p
    assert "relativeEntropyAreaSameObjectPhysicalReceiptStillRequired" in p


def test_quantum_rollup_registers_relative_entropy_bridge():
    p = text("DASHI/Quantum/Everything.agda")
    assert "import DASHI.Quantum.QuantumBirthmarkRelativeEntropyJacobsonSourceBridgeExact" in p
