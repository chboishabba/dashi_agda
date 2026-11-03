from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_source_sign_underdetermination_registered():
    path = ROOT / "DASHI/Quantum/QuantumBirthmarkEq223SourceSignUnderdeterminationExact.agda"
    assert path.exists()
    text = path.read_text()
    for token in [
        "positiveVacuumVariation",
        "negativeVacuumVariation",
        "positiveVacuumTraceIsFour",
        "negativeVacuumTraceIsMinusFour",
        "sameBareVariationTypeAllowsOppositeVacuumSigns",
        "eq223SourceTypeDoesNotDetermineVacuumSign",
        "sourceMetricVariationTheoremStillRequired",
    ]:
        assert token in text

    terminal = (ROOT / "DASHI/Quantum/QuantumBirthmarkHistoryDarkEnergyTerminalMaxCutExact.agda").read_text()
    assert "eq223SourceSignUnderdeterminationOwned" in terminal
