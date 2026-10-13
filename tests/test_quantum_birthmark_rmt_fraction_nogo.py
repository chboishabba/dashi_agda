from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_rmt_dark_energy_fraction_nogo_registered():
    path = ROOT / "DASHI/Quantum/QuantumBirthmarkRMTDarkEnergyFractionNoGoExact.agda"
    assert path.exists()
    text = path.read_text()
    for token in [
        "goeLargeNExcessFraction",
        "gueLargeNExcessFraction",
        "goeToObservedGapIsElevenSixHundredths",
        "goeFiniteN100ExcessFraction",
        "finiteNCorrectionMovesBelowTwoThirds",
        "rmtEnhancementCannotBeIdentifiedWithOmegaByThisNaiveMap",
    ]:
        assert token in text

    terminal = (ROOT / "DASHI/Quantum/QuantumBirthmarkHistoryDarkEnergyTerminalMaxCutExact.agda").read_text()
    assert "naiveRMTFractionNoGoOwned" in terminal
