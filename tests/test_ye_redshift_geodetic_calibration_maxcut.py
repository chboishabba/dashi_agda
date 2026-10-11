from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
MODULE = REPO_ROOT / "DASHI" / "Physics" / "Closure" / "BothwellYe2022GeodeticCalibrationExact.agda"
STATUS = REPO_ROOT / "DASHI" / "Physics" / "Closure" / "QuantumClockEmpiricalRedshiftIngestionStatusExact.agda"
ROLLUP = REPO_ROOT / "DASHI" / "Physics" / "Closure" / "YeRedshiftEverything.agda"


def read(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(REPO_ROOT)}"
    return path.read_text(encoding="utf-8")


def test_geodetic_calibration_pins_authoritative_noaa_artifact_and_same_object_gravity() -> None:
    text = read(MODULE)
    for marker in (
        "10.25923/zm69-rt94",
        "12022b3b7a632a71d966bed565bf61a7cc1abc2411d6d95702bc3116cdf13fd8069ff3a108ba0667135ff59607ead54e232f9ad75af51e8c222beeef76354454",
        "JILA S1B60H",
        "979607868.4 microGal",
        "sourceGravityNanoMetresPerSecondSquared = 9796078684",
        "paperRoundedGravityNanoMetresPerSecondSquared = 9796000000",
        "roundingResidualNanoMetresPerSecondSquared = 78684",
        "canonicalRoundingResidualWithinHalfMilliMetrePerSecondSquared",
        "geodeticArtifactChecksumRecorded = true",
        "experimentPaperArtifactChecksumRecorded = false",
        "rawExperimentArraysAcquired = false",
        "analysisCodeAcquired = false",
    ):
        assert marker in text


def test_later_2025_survey_is_provenance_update_not_retroactive_measurement_rewrite() -> None:
    text = read(MODULE)
    for marker in (
        "10.25923/8s2t-kh22",
        "f907622c980f8d7dedf3b2785c7ecfe0841e861f2197285e087545d852be2951f4505e96bfa1571d6eb5363569105336cb74bfcb8d1541512d921e251ea27a48",
        "laterSurveySupersedesNOSNGS77 = true",
        "laterSurveyRewritesPublished2022Calibration = false",
    ):
        assert marker in text


def test_ingestion_status_marks_geodetic_calibration_paid_without_overstating_experiment_artifact() -> None:
    text = read(STATUS)
    for marker in (
        "geodeticCalibrationIngested = true",
        "geodeticCalibrationChecksumIngested = true",
        "experimentPaperArtifactChecksumIngested = false",
        "rawExperimentArraysAcquired = false",
        "analysisCodeAcquired = false",
        "terminalSIMetrologyPromotionAllowed = false",
    ):
        assert marker in text


def test_rollup_imports_geodetic_calibration_once() -> None:
    rollup = read(ROLLUP)
    line = "import DASHI.Physics.Closure.BothwellYe2022GeodeticCalibrationExact"
    assert rollup.count(line) == 1
