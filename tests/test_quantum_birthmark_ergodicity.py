from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

SOURCE = ROOT / "DASHI/Quantum/QuantumBirthmarkSourceBoundaryExact.agda"
CORE = ROOT / "DASHI/Quantum/QuantumBirthmarkErgodicityExact.agda"
ROLLUP = ROOT / "DASHI/Quantum/Everything.agda"


def test_quantum_birthmark_source_boundary_is_pinned():
    text = SOURCE.read_text()
    assert "10.1103/dhzb-28rb" in text
    assert "Phys. Rev. X 16, 031063" in text
    assert "universalFactorWithoutTRS = 2" in text
    assert "universalFactorWithTRS = 3" in text
    assert "stadiumSimulationIsExampleNotUniversalProof = true" in text


def test_quantum_birthmark_core_reuses_quantum_dynamics():
    text = CORE.read_text()
    assert "DASHI.Physics.Laws.QuantumFieldLaws" in text
    assert "normPreserved" in text
    assert "UniversalBirthmarkFactor" in text
    assert "RevivalEnhancement" in text
    assert "maximumExplorationPrinciple" in text
    assert "birthmarkDoesNotByItselfRefuteThermodynamics" in text


def test_quantum_birthmark_rollup_registered():
    text = ROLLUP.read_text()
    assert "DASHI.Quantum.QuantumBirthmarkSourceBoundaryExact" in text
    assert "DASHI.Quantum.QuantumBirthmarkErgodicityExact" in text
