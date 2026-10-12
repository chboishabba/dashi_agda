from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_local_execution_receipts_are_pinned_and_non_promoting():
    owner = ROOT / "DASHI/Physics/Optics/DiffuserCamLocalExecutionReceiptExact.agda"
    text = owner.read_text(encoding="utf-8")
    assert "d7fa1547fadc1b052cb0e7dfe73fd94b6c2801579d225ba184b55290a8b8582c" in text
    assert "a6b0557ac982e0b29c5411623ce49e22d9372ae2043ca6b80fab06ccd092ce19" in text
    assert "syntheticOperatorReceiptCaptured = true" in text
    assert "claimScalePlannerReceiptCaptured = true" in text
    assert "realBerkeleyPSFReceiptCaptured = false" in text
    assert "physicalPhotonCalibrationReceiptCaptured = false" in text


def test_receipt_payloads_exist():
    for rel in (
        "receipts/optics/waller_diffusercam_synthetic_receipt.json",
        "receipts/optics/waller_diffusercam_claim_scale_receipt.json",
    ):
        assert (ROOT / rel).exists(), rel
