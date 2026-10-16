from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_berkeley_photon_transfer_owner_pins_executed_source_notebook():
    p = ROOT / "DASHI/Physics/Optics/BerkeleyPhotonTransferCalibrationExact.agda"
    text = p.read_text(encoding="utf-8")
    for marker in [
        "10.1364/OPTICA.570334",
        "f26873c2b58b82d84353bab2bf6edd478c5892a8",
        "2025_03_29_sec5_experimental_MI_photon_conversion.ipynb",
        "f8707b84dc696fc9218f6493467f0cda45193d3f",
        "rmlROIStartY = 500",
        "rmlROIEndY = 740",
        "rmlROIStartX = 1095",
        "rmlROIEndX = 1210",
        "diffuserROIStartY = 410",
        "diffuserROIEndY = 590",
        "diffuserROIStartX = 1100",
        "diffuserROIEndX = 1210",
        "lensedROIStartY = 500",
        "lensedROIEndY = 700",
        "lensedROIStartX = 1100",
        "lensedROIEndX = 1210",
        "rmlFitStartIndex = 150",
        "rmlFitEndExclusive = 250",
        "diffuserFitStartIndex = 150",
        "diffuserFitEndExclusive = 250",
        "lensFitStartIndex = 175",
        "lensFitEndExclusive = 250",
        'rmlDisplayedSlope = "0.02"',
        'rmlDisplayedIntercept = "1.46"',
        'diffuserDisplayedSlope = "0.03"',
        'diffuserDisplayedIntercept = "0.36"',
        'lensDisplayedSlope = "0.05"',
        'lensDisplayedIntercept = "0.01"',
        'digitalToPhotonFormula = "(image - intercept) / slope"',
        'photonConversionFormula = "clip((image - intercept) / slope, 0, infinity)"',
        "sourceExecutedPhotonTransferCalibrationPaid = true",
        "sourceDigitalToEstimatedPhotonConversionPaid = true",
        "localRawCalibrationSweepReexecuted = false",
        "incidentPhotonThroughputCalibrationPaid = false",
        "matchedPhysicalPhotonBudgetPaid = false",
    ]:
        assert marker in text


def test_calibration_is_exported_and_maxcut_keeps_source_and_local_execution_distinct():
    rollup = (ROOT / "DASHI/Physics/Optics/Everything.agda").read_text(encoding="utf-8")
    assert "BerkeleyPhotonTransferCalibrationExact" in rollup

    maxcut = (ROOT / "DASHI/Physics/Optics/Diffraction3DImagingAcquisitionMaxCutExact.agda").read_text(encoding="utf-8")
    assert "sourceExecutedPhotonTransferCalibrationPinned = true" in maxcut
    assert "sourceDigitalToEstimatedPhotonConversionPinned = true" in maxcut
    assert "localRawPhotonCalibrationReexecuted = PhotonTransfer.localRawCalibrationSweepReexecuted" in maxcut
    assert "incidentPhotonThroughputCalibrationPinned = PhotonTransfer.incidentPhotonThroughputCalibrationPaid" in maxcut
    assert "matchedPhotonAcrossParallelSystems = false" in maxcut
