from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_matched_control_experiment_donor_is_explicit_and_fail_closed():
    text = read("DASHI/Physics/ExoticGravity/AntigravityMatchedControlExperimentDonorMaxCutExact.agda")
    for token in (
        "sourceStateSwitchIsSynchronousModulationChannel",
        "conventionalStressRematchingRequired",
        "massGeometryPositionControlRequired",
        "electromagneticControlRequired",
        "thermalMechanicalOpticalVibrationControlRequired",
        "nullPreparationChannelRequired",
        "calibrationSignalRequired",
        "preregisteredAnalysisRequired",
        "numericalSystematicsBudgetStillRequired",
        "physicalMatchedSourceSwitchStillRequired",
        "birthmarkHistoryIdentifiedWithCMP119VacuumCoordinate",
    ):
        assert token in text


def test_historical_ybco_null_is_a_constraint_not_a_same_apparatus_payment():
    text = read("DASHI/Physics/ExoticGravity/AntigravityMatchedControlExperimentDonorMaxCutExact.agda")
    for token in (
        "LiTorrStaticNullBoundBidiExact",
        "historicalStaticYBCONullConstraintAvailable",
        "candidateMustRespectHistoricalStaticYBCOBound",
        "historicalStaticNullPaysNewSameApparatusReceipt",
        "historicalStaticNullPaysNewSameApparatusReceiptIsFalse",
        "exactHistoricalGeometryMayReplaceNewDeviceGeometry",
        "exactHistoricalGeometryMayReplaceNewDeviceGeometryIsFalse",
    ):
        assert token in text
