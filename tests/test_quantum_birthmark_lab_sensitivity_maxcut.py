from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_quantum_birthmark_lab_sensitivity_maxcut_registered():
    script = ROOT / "scripts/quantum_birthmark_lab_sensitivity.py"
    source = ROOT / "DASHI/Quantum/QuantumBirthmarkLaboratorySensitivitySourceAtlasExact.agda"
    model = ROOT / "DASHI/Quantum/QuantumBirthmarkLaboratorySensitivityExact.agda"
    systematics = ROOT / "DASHI/Quantum/QuantumBirthmarkLaboratorySystematicsExact.agda"
    terminal = ROOT / "DASHI/Quantum/QuantumBirthmarkLaboratorySensitivityMaxCutExact.agda"

    for path in [script, source, model, systematics, terminal]:
        assert path.exists()

    script_text = script.read_text()
    for token in [
        "TorsionBenchmark",
        "AtomInterferometerBenchmark",
        "OptomechanicalBenchmark",
        "two_sigma_fractional_transfer",
        "required_hours",
        "history_only_signal",
        "required_fractional_precision_improvement",
        "white_noise_time_multiplier",
    ]:
        assert token in script_text

    source_text = source.read_text()
    for token in [
        "milligramTorsion2026",
        "latticeAtomInterferometer2024",
        "quantumReadyOptomechanics2026",
        "currentExperimentsDidNotTestHistoryConditioning",
    ]:
        assert token in source_text

    model_text = model.read_text()
    for token in [
        "torsionPointMassNewtonianForceAttoNewtonRounded",
        "torsionTwoSigmaFractionalTransfer",
        "atomOneSigmaFractionalTransferSquared",
        "optoTenPercentUnitSNRUpperHours",
        "optoOnePercentUnitSNRUpperHours",
        "onePercentFiveSigmaTimePenalty",
        "transferSensitivityIsNotHistoryConstraint",
        "nonzeroHistoryCouplingStillNotPredicted",
    ]:
        assert token in model_text

    systematics_text = systematics.read_text()
    for token in [
        "MatchedHistorySystematicsCut",
        "conventionalStressRematchingAfterHistoryPreparation",
        "electrostaticPatchAndChargeControl",
        "thermalAndMechanicalStateControl",
        "synchronousHistoryModulationRequired",
        "numericalSystematicsBudgetClosed",
    ]:
        assert token in systematics_text

    terminal_text = terminal.read_text()
    for token in [
        "classicalMilligramTransferBenchmarkOwned",
        "atomInterferometerTransferBenchmarkOwned",
        "quantumReadyOptomechanicalScalingOwned",
        "instrumentTransferSensitivityOwned",
        "systematicsCutOwned",
        "genericBenchmarkReferences",
        "birthmarkLaboratoryPredictionRequest",
        "historySignalMagnitudeStillRequiresMicroscopicCoupling",
        "matchedHistorySystematicsBudgetStillRequired",
        "actualHistoryConditionedMeasurementStillRequired",
    ]:
        assert token in terminal_text

    rollup = (ROOT / "DASHI/Quantum/Everything.agda").read_text()
    for name in [
        "QuantumBirthmarkLaboratorySensitivitySourceAtlasExact",
        "QuantumBirthmarkLaboratorySensitivityExact",
        "QuantumBirthmarkLaboratorySystematicsExact",
        "QuantumBirthmarkLaboratorySensitivityMaxCutExact",
    ]:
        assert name in rollup
