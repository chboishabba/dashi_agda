import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OWNER = ROOT / "DASHI/Physics/Optics/BerkeleyDiffuserCamRealConditioningExecutionExact.agda"
RECEIPT = ROOT / "receipts/optics/waller_diffusercam_real_conditioning_receipt.json"


def test_real_conditioning_receipt_pins_exact_waller_artifact_and_execution():
    data = json.loads(RECEIPT.read_text(encoding="utf-8"))
    assert data["artifact_git_blob_sha1"] == "db59065bdaf44fe771a6d3fbe22ae3c703527b5f"
    assert data["artifact_bytes"] == 10823885
    assert data["artifact_sha256"] == "fdbc8b2c7a8753f146e1b270a3f0ae2d0f70cb2c4ff49aef4a926670c0f7c906"
    assert data["psf_shape"] == [270, 320, 44]
    assert data["numerical_rank"] == 44
    assert data["selected_source_h_family"]["column_count"] == 396
    assert data["selected_source_h_family"]["lateral_radius_pixels"] == 1
    assert data["selected_source_h_family"]["lateral_step_pixels"] == 1
    assert data["selected_source_h_family"]["fft_vs_roll_max_abs_error_first_column"] < 1e-12
    assert data["max_scene_sparsity_for_positive_bound"] == 1
    assert data["global_sparse_inverse_certificate"] is True
    assert data["all_resolution_camera_rip_certificate"] is False
    assert data["matched_photon_comparison"] is False


def test_real_conditioning_owner_promotes_only_declared_finite_same_h_receipt():
    text = OWNER.read_text(encoding="utf-8")
    assert "realPSFArtifactBytesVerified = true" in text
    assert "depthOnlyNumericalReceiptCaptured = true" in text
    assert "translatedColumnNumericalReceiptCaptured = true" in text
    assert "finiteSelectedFamilyRestrictedKappaPaid = true" in text
    assert "allResolutionCameraRIPPaid = false" in text
    assert "matchedPhotonComparisonPaid = false" in text
    assert "maxSceneSparsityPositiveBound = 1" in text
