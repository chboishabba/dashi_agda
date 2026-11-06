from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DASHI = REPO_ROOT / "DASHI"
MODULE = DASHI / "Physics" / "Closure" / "BothwellYe2022ChronometricGeodesyBridgeExact.agda"
STATUS = DASHI / "Physics" / "Closure" / "QuantumClockEmpiricalRedshiftIngestionStatusExact.agda"
ROLLUP = DASHI / "Physics" / "Closure" / "YeRedshiftEverything.agda"


def read(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(REPO_ROOT)}"
    return path.read_text(encoding="utf-8")


def test_chronometric_geodesy_uses_same_clock_gravity_and_si_metre_carriers() -> None:
    text = read(MODULE)
    for marker in (
        "canonicalPublishedGradientPayload",
        "canonicalBothwellYe2022GeodeticCalibrationReceipt",
        "canonicalQuantumClockProperTimeRedshiftBridge",
        "canonicalSIMetreFromSecondAndCAdapter",
        "fractionalFrequencyUncertaintyUnits1eMinus22 = 76",
        "speedOfLightInteger = 299792458",
        "sourceGravityNanoMetresPerSecondSquared = 9796078684",
        "heightEquivalentMicrometreNumerator = 6830539358399814064",
        "heightEquivalentMicrometreDenominator = 97960786840000000",
        "canonicalHeightEquivalentAtLeast69Micrometres",
        "canonicalHeightEquivalentAtMost70Micrometres",
    ):
        assert marker in text


def test_height_equivalent_is_not_promoted_to_geodetic_accuracy() -> None:
    text = read(MODULE)
    for marker in (
        "heightEquivalentScaleDerived = true",
        "sameObjectClockGravityMetreWeld = true",
        "heightEquivalentClaimedAsElevationAccuracy = false",
        "rawExperimentDataRequiredForAccuracyPromotion = true",
        "fullCovarianceRequiredForAccuracyPromotion = true",
        "chronometricGeodesyPromotionAllowed = false",
    ):
        assert marker in text


def test_ingestion_status_records_bridge_without_opening_terminal_gate() -> None:
    text = read(STATUS)
    for marker in (
        "chronometricGeodesyBridgeConstructed = true",
        "heightEquivalentScaleConstructed = true",
        "chronometricGeodesyPromotionAllowed = false",
        "terminalSIMetrologyPromotionAllowed = false",
    ):
        assert marker in text


def test_rollup_imports_chronometric_geodesy_bridge_once() -> None:
    rollup = read(ROLLUP)
    line = "import DASHI.Physics.Closure.BothwellYe2022ChronometricGeodesyBridgeExact"
    assert rollup.count(line) == 1
