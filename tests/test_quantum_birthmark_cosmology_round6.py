from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_birthmark_cosmology_round6_registered():
    expected = {
        "DASHI/Quantum/QuantumBirthmarkH2EquationOfStateUnderdeterminationExact.agda": [
            "constantH2GivesVacuumW",
            "unitScalingH2GivesMinusTwoThirds",
            "hubbleSquaredTrackingDoesNotFixEquationOfState",
            "microscopicExpansionHistoryStillRequired",
        ],
        "DASHI/Quantum/QuantumBirthmarkOmegaUnderdeterminationExact.agda": [
            "lowModelOmega",
            "highModelOmega",
            "omegaNotFixedByHorizonNormalization",
            "observedOmegaRequiresMicroscopicFraction",
        ],
        "DASHI/Quantum/QuantumBirthmarkPotentialCouplingBenchmarkExact.agda": [
            "historyActionGap",
            "actionGapSelectsDifferentVacuumEnergies",
            "finitePotentialCouplingBenchmarkOwned",
            "sourceNativeCMP119CouplingStillRequired",
        ],
        "DASHI/Quantum/QuantumBirthmarkSIStressCalibrationExact.agda": [
            "criticalDensityReferenceEminus27",
            "calibratedHistoryDensityEminus27",
            "calibratedHistoryDensityIsReferenceFraction",
            "siMagnitudeTransferOwned",
            "sourceNativeMagnitudePredictionStillRequired",
        ],
    }
    for rel, tokens in expected.items():
        path = ROOT / rel
        assert path.exists(), rel
        text = path.read_text()
        for token in tokens:
            assert token in text, (rel, token)

    terminal = (ROOT / "DASHI/Quantum/QuantumBirthmarkHistoryDarkEnergyTerminalMaxCutExact.agda").read_text()
    for token in [
        "h2EquationOfStateUnderdeterminationOwned",
        "omegaUnderdeterminationOwned",
        "finitePotentialCouplingBenchmarkOwned",
        "siMagnitudeTransferOwned",
    ]:
        assert token in terminal
