from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_local_photon_transfer_script_and_receipt_are_non_promoting():
    script = (ROOT / "scripts/check_berkeley_photon_transfer_calibration.py").read_text(encoding="utf-8")
    for marker in [
        "np.random.default_rng",
        "linregress",
        "variance_vs_mean",
        "(digital - intercept) / slope",
        '"raw_berkeley_sweep_reexecuted": False',
        '"incident_throughput_calibrated": False',
    ]:
        assert marker in script

    owner = (ROOT / "DASHI/Physics/Optics/BerkeleyPhotonTransferLocalExecutionReceiptExact.agda").read_text(encoding="utf-8")
    assert "localSyntheticPhotonTransferReceiptCaptured = true" in owner
    assert "rawBerkeleySweepReexecuted = false" in owner
    assert "incidentThroughputCalibrationPaid = false" in owner
    assert "matchedPhysicalPhotonBudgetPaid = false" in owner


def test_local_photon_transfer_receipt_is_exported_and_welded_to_maxcut():
    receipt = ROOT / "receipts/optics/berkeley_photon_transfer_synthetic_receipt.json"
    assert receipt.exists()
    rollup = (ROOT / "DASHI/Physics/Optics/Everything.agda").read_text(encoding="utf-8")
    assert "BerkeleyPhotonTransferLocalExecutionReceiptExact" in rollup
    maxcut = (ROOT / "DASHI/Physics/Optics/Diffraction3DImagingAcquisitionMaxCutExact.agda").read_text(encoding="utf-8")
    assert "localSyntheticPhotonTransferReceiptCaptured" in maxcut
