from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_lab_coupling_calibration_nogo_registered():
    path = ROOT / "DASHI/Quantum/QuantumBirthmarkLaboratoryCouplingUnderdeterminationExact.agda"
    assert path.exists()
    text = path.read_text()
    for token in [
        "finiteVacuumAmplitudeGap",
        "unitCalibrationEpsilon",
        "doubleCalibrationEpsilon",
        "sameFiniteGapAllowsDifferentLaboratoryCouplings",
        "finiteAmplitudeGapIsNotForceFractionByDefinition",
        "microscopicMetricToObservableCalibrationStillRequired",
    ]:
        assert token in text

    terminal = (ROOT / "DASHI/Quantum/QuantumBirthmarkHistoryDarkEnergyTerminalMaxCutExact.agda").read_text()
    assert "laboratoryCouplingUnderdeterminationOwned" in terminal
