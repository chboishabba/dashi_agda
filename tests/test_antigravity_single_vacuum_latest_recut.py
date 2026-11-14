from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_single_vacuum_geometry_reuses_one_source_scale():
    text = read("DASHI/Physics/Foundations/GRQFTCMP119SingleSourceVacuumKottlerRouteExact.agda")
    for token in (
        "SingleSourceVacuum",
        "sourceAmplitude",
        "singleSourceVacuumStress",
        "SingleSourceVacuumKottlerCandidate",
        "secondSourceVacuumScaleRequired",
        "physicalMetricAmplitudeWeldStillRequired",
    ):
        assert token in text


def test_single_vacuum_safe_band_and_scale_covariance():
    safe = read("DASHI/Physics/Foundations/GRQFTSingleVacuumSafeBandExact.agda")
    scale = read("DASHI/Physics/Foundations/GRQFTSingleVacuumNormalizationScaleCovarianceExact.agda")
    for token in ("conicQ", "sourceQSafeLower", "sourceQSafeUpper", "conicHomogeneousIdentity"):
        assert token in safe
    for token in ("rescaledVacuumAmplitude", "conicQNormalizationScaleCovariant", "unknownMultiplicativeMagnitudeBlocksGeometricExistence"):
        assert token in scale


def test_differential_common_counterterm_and_metric_response():
    renorm = read("DASHI/Physics/Foundations/GRQFTVacuumAmplitudeDifferentialRenormalizationExact.agda")
    metric = read("DASHI/Physics/ExoticGravity/AntigravitySingleVacuumDifferentialMetricCompilerExact.agda")
    for token in (
        "commonCountertermCancelsInDifference",
        "physicalVacuumDifferenceIsMultiplicativeSourceDifference",
        "modulatedVacuumDifferenceNeedsAbsoluteAdditiveZero",
        "sourceDifferenceCanDriveLockInLaneModuloCalibration",
    ):
        assert token in renorm
    for token in (
        "kottlerMetricTTDeltaIsRadiusSquaredThirdDeltaLambda",
        "sourceModulationMetricTTDeltaIsCalibratedSourceDifference",
        "scalarMetricPerturbationAlreadyEqualsSchutzholdTTMode",
    ):
        assert token in metric


def test_physical_promotion_keeps_real_source_physics_open():
    text = read("DASHI/Physics/ExoticGravity/AntigravitySingleVacuumPhysicalPromotionMaxCutExact.agda")
    for token in (
        "selectedCMP119VacuumContinuationWeldStillOpen",
        "unknownPositiveMultiplicativeMagnitudeBlocksStaticExistence",
        "additiveStaticVacuumRenormalizationStillOpen",
        "physicalControlToVacuumAmplitudeStillOpen",
        "fullPhysicalDeviceDemonstrated",
    ):
        assert token in text


def test_latest_scheduler_has_three_alternative_routes():
    text = read("DASHI/Physics/ExoticGravity/AntigravitySourceNativeShortestPathMaxCutExact.agda")
    for token in (
        "SingleVacuumStaticRouteBoundary",
        "DifferentialLockInRouteBoundary",
        "ContinuumStressRouteBoundary",
        "twoSourceVacuumAdmissionRequiredForStaticShortestPath",
        "absoluteStaticLambdaRequiredForDifferentialLockIn",
        "r136FiniteContinuumResponseWeldRequiredForStaticVacuumRoute",
        "physicalControlAndSICalibrationStillRequired",
    ):
        assert token in text
