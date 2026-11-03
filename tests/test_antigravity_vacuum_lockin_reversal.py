from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_reversal_estimator_cancels_common_background_and_recovers_signal():
    text = read(
        "DASHI/Physics/Foundations/GRQFTVacuumLockInReversalEstimatorExact.agda"
    )
    for token in (
        "oddEstimator",
        "evenEstimator",
        "oddEstimatorRecoversSignal",
        "evenEstimatorRecoversCommonBackground",
        "vacuumOddEstimatorRecoversPhysicalDifference",
        "vacuumOddEstimatorIsCalibratedSourceDifference",
        "legacyPhysicalVacuumDifferenceNameIsNotYetGravitationalDeltaLambda",
        "metricResponseOddEstimatorRecoversPhysicalDeltaLambda",
        "metricResponseOddEstimatorIsScaledNormalizationDifference",
        "reversalParityStillNeedsPhysicalReceipt",
    ):
        assert token in text


def test_post_normalization_scheduler_imports_lockin_estimator():
    text = read(
        "DASHI/Physics/ExoticGravity/AntigravityPostNormalizationMaxCutExact.agda"
    )
    assert "GRQFTVacuumLockInReversalEstimatorExact" in text
    assert "differentialReversalEstimatorAlgebraOwned" in text
    assert "differentialPhysicalDeltaLambdaLockInAlgebraOwnedAfterReceipt" in text
