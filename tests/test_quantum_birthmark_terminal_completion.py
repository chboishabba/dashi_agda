from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OWNER = ROOT / "DASHI/Quantum/QuantumBirthmarkTerminalCompletionExact.agda"
ROLLUP = ROOT / "DASHI/Quantum/Everything.agda"


def test_terminal_completion_has_only_explicit_residual_classes():
    text = OWNER.read_text()
    assert "data ResidualCategory" in text
    assert "sourceModelInstantiation" in text
    assert "authorityInstantiation" in text
    assert "empiricalCalibration" in text
    assert "noFurtherFormalCompositionDebt" in text
    assert "noGenericWeldResidualCategory" in text


def test_terminal_completion_includes_entropy_density_expansion_spine():
    text = OWNER.read_text()
    for token in [
        "entropyDensityExpansionCompilerOwned",
        "preferredResidualEq223ExpansionCompilerOwned",
        "antigravityExpansionTerminalOwned",
        "positiveGRepulsionAndExpansionEndpointsOwned",
        "allExistingGravityExpansionPriorArtCrossPollinated",
    ]:
        assert token in text


def test_terminal_completion_registered():
    assert "QuantumBirthmarkTerminalCompletionExact" in ROLLUP.read_text()
