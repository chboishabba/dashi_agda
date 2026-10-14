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
        "roiStartY = 180",
        "roiEndY = 480",
        "roiStartX = 100",
        "roiEndX = 700",
        "rmlFitStart = 150",
        "rmlFitEnd = 250",
        "diffuserFitStart = 150",
        "diffuserFitEnd = 250",
        "lensedFitStart = 175",
        "lensedFitEnd = 250",
        'rmlReportedSlope = "0.1898"',
        'rmlReportedR2 = "0.7806"',
        'diffuserReportedSlope = "0.1872"',
        'diffuserReportedR2 = "0.9560"',
        'lensedReportedSlope = "0.1807"',
        'lensedReportedR2 = "0.9994"',
        'digitalToPhotonFormula = "(image - intercept) / slope"',
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
    assert "localRawPhotonCalibrationReexecuted = false" in maxcut
    assert "incidentPhotonThroughputCalibrationPinned = false" in maxcut
    assert "matchedPhotonAcrossParallelSystems = false" in maxcut
