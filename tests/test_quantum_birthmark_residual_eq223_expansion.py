from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_residual_eq223_expansion_registered():
    owner = (ROOT / "DASHI/Quantum/QuantumBirthmarkResidualEq223ExpansionExact.agda").read_text()
    rollup = (ROOT / "DASHI/Quantum/Everything.agda").read_text()
    for token in [
        "ResidualEq223BalanceInstantiation",
        "selectedResidualSectorMapsToRound132Density",
        "residualBalanceMatchesEq223FourSectorBalance",
        "residualPositiveBalanceForcesPositiveMatterAcceleration",
        "preferredBalabanSignConventionReused",
        "gammaMinusLogZNotIntroduced",
        "residualEq223ToExpansionCompositionClosed",
    ]:
        assert token in owner
    assert "CMP119CosmologyBalabanPreferredSignToExpansionExact" in owner
    assert "QuantumBirthmarkResidualEq223ExpansionExact" in rollup
