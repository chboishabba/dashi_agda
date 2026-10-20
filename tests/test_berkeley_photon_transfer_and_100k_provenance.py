from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_photon_transfer_owner_pins_executed_three_camera_calibration_and_keeps_throughput_separate():
    p = ROOT / "DASHI/Physics/Optics/BerkeleyPhotonTransferCalibrationExact.agda"
    text = p.read_text(encoding="utf-8")
    for marker in (
        "f8707b84dc696fc9218f6493467f0cda45193d3f",
        "photonCountCalibrationDriveFolder",
        "rmlDisplayedSlope = \"0.02\"",
        "rmlDisplayedIntercept = \"1.46\"",
        "diffuserDisplayedSlope = \"0.03\"",
        "diffuserDisplayedIntercept = \"0.36\"",
        "lensDisplayedSlope = \"0.05\"",
        "lensDisplayedIntercept = \"0.01\"",
        "photonConversionFormula = \"clip((image - intercept) / slope, 0, infinity)\"",
        "sourceExecutedPhotonTransferCalibrationPaid = true",
        "simultaneousThreeCameraSweepPinned = true",
        "detectedPhotonCountConversionPinned = true",
        "fullPrecisionFitCoefficientsRecovered = false",
        "opticalThroughputCalibrationPaid = false",
        "matchedIncidentPhotonBudgetPaid = false",
    ):
        assert marker in text


def test_100k_release_provenance_owner_pins_main_dataset_and_release_lineage_without_inventing_run_log():
    p = ROOT / "DASHI/Physics/Optics/BerkeleyPLD100kReleaseProvenanceExact.agda"
    text = p.read_text(encoding="utf-8")
    for marker in (
        "1CqPliG5rZIYH5zA6cXdrA6cvDF7obbvc",
        "1YLSHYeM7jJeAMJpNxtArQRKj13QIjtqj",
        "13tVwvJv_WaoXPwVejLqQsDcNk9AyEj3s",
        "18Pf3n41IFBhbKKSddmK58iv5l0FX8ZyY",
        "AWB 100k Dataset - SEPARATE DATASET",
        "AWB 25k Dataset - SEPARATE DATASET",
        "releaseCaptureDiffuserExposureUs = 25000",
        "releaseCaptureRMLExposureUs = 80000",
        "releaseCaptureGroundTruthExposureUs = 18000",
        "releaseCaptureGainZeroPaid = true",
        "main100kArchiveIdentityPinned = true",
        "releaseLineageCaptureParametersPinned = true",
        "exactArchiveRunLogRecovered = false",
        "exactArchiveExposureSameRunPaid = false",
    ):
        assert marker in text


def test_rollup_and_acquisition_maxcut_consume_new_physical_receipts():
    rollup = (ROOT / "DASHI/Physics/Optics/Everything.agda").read_text(encoding="utf-8")
    assert "BerkeleyPhotonTransferCalibrationExact" in rollup
    assert "BerkeleyPLD100kReleaseProvenanceExact" in rollup

    maxcut = (ROOT / "DASHI/Physics/Optics/Diffraction3DImagingAcquisitionMaxCutExact.agda").read_text(encoding="utf-8")
    assert "sourceExecutedPhotonTransferCalibrationPinned" in maxcut
    assert "detectedPhotonCountConversionPinned" in maxcut
    assert "main100kArchiveIdentityPinned" in maxcut
    assert "releaseLineageCaptureParametersPinned" in maxcut
    assert "exactArchiveExposureSameRunPaid" in maxcut
    assert "opticalThroughputCalibrationPinned" in maxcut
