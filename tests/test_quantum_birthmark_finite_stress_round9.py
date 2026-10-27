from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_finite_birthmark_stress_compiler_registered():
    path = ROOT / "DASHI/Quantum/QuantumBirthmarkFiniteVacuumStressExact.agda"
    assert path.exists()
    text = path.read_text()
    for token in [
        "birthmarkVacuumStress",
        "lowBirthmarkStress00",
        "lowBirthmarkStress11",
        "highBirthmarkStress00",
        "highBirthmarkStress11",
        "finiteBirthmarkToVacuumStressOwned",
        "sourceNativeMetricVariationStillRequired",
    ]:
        assert token in text

    terminal = (ROOT / "DASHI/Quantum/QuantumBirthmarkHistoryDarkEnergyTerminalMaxCutExact.agda").read_text()
    assert "finiteBirthmarkToVacuumStressOwned" in terminal
