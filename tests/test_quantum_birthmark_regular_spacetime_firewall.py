from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_regular_spacetime_thin_shell_firewall_registered():
    path = ROOT / "DASHI/Quantum/QuantumBirthmarkThinShellRegularityFirewallExact.agda"
    assert path.exists()
    text = path.read_text()
    for token in [
        "interiorCurvatureInvariantsFinite",
        "positiveHorizonExistenceSourceWritten",
        "israelShellCarriesDistributionalStress",
        "thinShellIsNotSmoothFiniteThicknessWall",
        "globalSmoothRegularBlackHoleNotPromoted",
        "finiteThicknessOrDistributionalRegularityTheoremRequired",
    ]:
        assert token in text

    terminal = (ROOT / "DASHI/Quantum/QuantumBirthmarkHistoryDarkEnergyTerminalMaxCutExact.agda").read_text()
    assert "thinShellRegularityFirewallOwned" in terminal
