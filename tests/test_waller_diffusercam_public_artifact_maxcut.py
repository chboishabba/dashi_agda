from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_public_artifact_owner_exists():
    p = ROOT / "DASHI/Physics/Optics/WallerDiffuserCamPublicArtifactExact.agda"
    text = p.read_text()
    assert "example_psfs.mat" in text
    assert "db59065bdaf44fe771a6d3fbe22ae3c703527b5f" in text
    assert "example_raw.png" in text
    assert "c8516cb8f482c2bb15e75ebebd91a74b88732c95" in text
    assert "publicPSFStackPresent = true" in text
    assert "publicRawExposurePresent = true" in text


def test_code_forward_owner_pins_literal_reconstruction_semantics():
    p = ROOT / "DASHI/Physics/Optics/WallerDiffuserCamCodeForwardExact.agda"
    text = p.read_text()
    for marker in [
        "psfBias102",
        "imageBias100",
        "fftConvolutionForward",
        "fftConvolutionAdjoint",
        "nonnegativeReconstruction",
        "tvRegularisationAvailable",
        "nativeSparsityAvailable",
    ]:
        assert marker in text


def test_conditioning_acquisition_script_is_exact_artifact_scoped():
    p = ROOT / "scripts/check_waller_diffusercam_conditioning.py"
    text = p.read_text()
    assert "example_psfs.mat" in text
    assert "c8516cb8f482c2bb15e75ebebd91a74b88732c95" in text
    assert "psf_bias = 102.0" in text
    assert "depth_only_same_lateral" in text
    assert "global_sparse_inverse_certificate" in text
    assert "False" in text


def test_conditioning_owner_keeps_depth_diagnostic_separate_from_global_kappa():
    p = ROOT / "DASHI/Physics/Optics/WallerDiffuserCamDepthConditioningExact.agda"
    text = p.read_text()
    assert "depthOnlySameLateralDiagnosticPaid = true" in text
    assert "globalSparseRestrictedKappaPaid = false" in text
    assert "publishedPSFArtifactUsed = true" in text


def test_optics_rollup_and_maxcut_include_public_artifact_tranche():
    rollup = (ROOT / "DASHI/Physics/Optics/Everything.agda").read_text()
    for mod in [
        "WallerDiffuserCamPublicArtifactExact",
        "WallerDiffuserCamCodeForwardExact",
        "WallerDiffuserCamDepthConditioningExact",
    ]:
        assert mod in rollup

    maxcut = (ROOT / "DASHI/Physics/Optics/Diffraction3DImagingPhysicalMaxCutExact.agda").read_text()
    assert "publicCalibrationArtifactPaid = true" in maxcut
    assert "publicForwardCodeReceiptPaid = true" in maxcut
    assert "depthConditioningDiagnosticPaid = true" in maxcut
    assert "globalRestrictedKappaPaid = false" in maxcut
    assert "matchedPhotonExperimentPaid = false" in maxcut
