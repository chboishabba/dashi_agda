from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_birthmark_microscopic_round5_registered():
    expected = {
        "DASHI/Quantum/QuantumBirthmarkNormalizedFiniteHistoryWeightExact.agda": [
            "lowBirthmarkWeightsNormalize",
            "highBirthmarkWeightsNormalize",
            "symmetricWeightsNormalize",
            "normalizedWeightLawNotUnique",
            "normalizedFiniteWeightModelOwned",
        ],
        "DASHI/Quantum/QuantumBirthmarkFiniteOrderParameterCouplingExact.agda": [
            "lowBirthmarkOrderParameter",
            "highBirthmarkOrderParameter",
            "lowBirthmarkVacuumEnergy",
            "highBirthmarkVacuumEnergy",
            "finiteBirthmarkToOrderParameterCouplingOwned",
            "continuumBirthmarkStatisticsLawStillRequired",
        ],
        "DASHI/Quantum/QuantumBirthmarkFiniteHorizonFractionExact.agda": [
            "historyFraction",
            "historyDensityTracksCriticalDensity",
            "finiteHistoryFractionModelOwned",
            "historyFractionIsNotObservedOmegaByDefinition",
        ],
        "DASHI/Quantum/QuantumBirthmarkD1UnderdeterminationExact.agda": [
            "BareFirstVariation",
            "zeroVariation",
            "nonzeroVariation",
            "bareFunctionDoesNotDetermineLinearityLaws",
            "sourceInterfaceStrengtheningStillRequired",
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
        "normalizedFiniteWeightModelOwned",
        "finiteBirthmarkToOrderParameterCouplingOwned",
        "finiteHistoryFractionModelOwned",
        "d1UnderdeterminationWitnessOwned",
    ]:
        assert token in terminal
