from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_local_execution_receipts_are_pinned_and_non_promoting():
    owner = ROOT / "DASHI/Physics/Optics/DiffuserCamLocalExecutionReceiptExact.agda"
    text = owner.read_text(encoding="utf-8")
    assert "128d24378b12a055282ffccb813744e626b846e1" in text
    assert "52cecec7a7b61fc5577129e9b704ee53482f2c82" in text
    assert "gershgorinSupportsChecked = 22218" in text
    assert "gershgorinBoundViolations = 0" in text
    assert "exhaustiveFiniteSupportReceiptCaptured = true" in text
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
