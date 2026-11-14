from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_source_potential_underdetermination_registered():
    path = ROOT / "DASHI/Quantum/QuantumBirthmarkCMP119PotentialUnderdeterminationExact.agda"
    assert path.exists()
    text = path.read_text()
    for token in [
        "ignoreVacuumAlgebra",
        "includeVacuumAlgebra",
        "sameRawActionAlgebraTypeAllowsDifferentVacuumCoupling",
        "rawCMP119ActionTypeDoesNotDetermineHistoryPotentialCoupling",
        "sourceNativePotentialCouplingTheoremStillRequired",
    ]:
        assert token in text

    terminal = (ROOT / "DASHI/Quantum/QuantumBirthmarkHistoryDarkEnergyTerminalMaxCutExact.agda").read_text()
    assert "cmp119PotentialCouplingUnderdeterminationOwned" in terminal
