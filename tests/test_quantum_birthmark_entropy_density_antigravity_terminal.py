from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_entropy_density_antigravity_terminal_registered():
    owner = (ROOT / "DASHI/Quantum/QuantumBirthmarkEntropyDensityAntigravityTerminalExact.agda").read_text()
    rollup = (ROOT / "DASHI/Quantum/Everything.agda").read_text()
    for token in [
        "EntropyDensityAntigravityTerminalReceipt",
        "residualToCMP119ExpansionCompilerOwned",
        "localizedPositiveGAntigravityWitnessReused",
        "finiteFLRWExpansionWitnessReused",
        "balancedDECRepulsiveShellFamilyRegistered",
        "decRepulsiveExteriorBranchRegistered",
        "nambuGotoRepulsiveBubbleBranchRegistered",
        "positiveGravityCouplingRetained",
        "negativeGravityConstantNotRequired",
        "negativeInertialMassNotRequired",
        "birthmarkPersistenceDoesNotFixTraceSign",
        "allExistingAntigravityExpansionContentCrossPollinated",
        "noAdditionalGravityMechanismNeededForSteelman",
        "steelmanFormalProgrammeClosed",
    ]:
        assert token in owner
    assert "GRQFTLocalizedAntigravityMaxCutExact" in owner
    assert "GRQFTFiniteFLRWRepulsiveAccelerationExact" in owner
    assert "GRQFTBalancedDECRepulsiveShellFamilyExact" in owner
    assert "GRQFTDECRepulsiveExteriorMaxCutExact" in owner
    assert "GRQFTNambuGotoRepulsiveBubbleMaxCutExact" in owner
    assert "QuantumBirthmarkEntropyDensityAntigravityTerminalExact" in rollup
