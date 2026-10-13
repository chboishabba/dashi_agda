from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_birthmark_source_dynamics_round3_registered():
    expected = {
        "DASHI/Quantum/QuantumBirthmarkCommonHistoryIdentityBenchmarkExact.agda": [
            "identityHistoryMap",
            "selectedBirthmarkHistoryMapsByRefl",
            "commonHistoryMapBenchmarkOwned",
        ],
        "DASHI/Quantum/QuantumBirthmarkEq223SharpThresholdBridgeExact.agda": [
            "sharpVacuumThresholdReused",
            "preferredTwoLeafSignIsWeakerThanSharpThreshold",
            "sharpThresholdCompilesToExpansion",
        ],
        "DASHI/Quantum/QuantumBirthmarkDeSitterCoreCurvatureExact.agda": [
            "coreRicciScalarIsThreeHalves",
            "coreRicciSquareIsNineSixteenths",
            "coreKretschmannIsThreeEighths",
            "boundedCoreCurvatureInvariantsOwned",
        ],
        "DASHI/Quantum/QuantumBirthmarkFiniteHistoryWeightWitnessExact.agda": [
            "finiteBirthmarkWeightSelection",
            "historyABCWeight",
            "historyACBWeight",
            "finiteMicroscopicWeightWitnessOwned",
            "finiteWitnessIsNotContinuumLaw",
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
        "commonHistoryIdentityBenchmarkOwned",
        "finiteBirthmarkWeightWitnessOwned",
        "sharpEq223ThresholdBridgeOwned",
        "boundedCoreCurvatureInvariantsOwned",
    ]:
        assert token in terminal

    rollup = (ROOT / "DASHI/Quantum/Everything.agda").read_text()
    for name in [
        "QuantumBirthmarkCommonHistoryIdentityBenchmarkExact",
        "QuantumBirthmarkEq223SharpThresholdBridgeExact",
        "QuantumBirthmarkDeSitterCoreCurvatureExact",
        "QuantumBirthmarkFiniteHistoryWeightWitnessExact",
    ]:
        assert name in rollup
