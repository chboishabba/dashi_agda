from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_existing_berkeley_public_artifact_owner_is_source_pinned():
    p = ROOT / "DASHI/Physics/Optics/BerkeleyDiffuserCamPublicCalibrationExact.agda"
    text = p.read_text()
    assert "example_psfs.mat" in text
    assert "db59065bdaf44fe771a6d3fbe22ae3c703527b5f" in text
    assert "example_raw.png" in text
    assert "3b4c3b2ca674bbd21d925a1f0a1ea79a77efe5df" in text
    assert "c8516cb8f482c2bb15e75ebebd91a74b88732c95" in text
    assert "publicCalibrationArtifactPinned = true" in text


def test_existing_source_operator_owner_pins_literal_reconstruction_semantics():
    p = ROOT / "DASHI/Physics/Optics/BerkeleyDiffuserCamSourceOperatorExact.agda"
    text = p.read_text()
    for marker in [
        "psfBias",
        "imageBias",
        "sourceForwardUsesFFTConvolution = true",
        "sourceUsesDepthFlipAndShift = true",
        "sourceNormalisesPSFStack = true",
        "sourceUsesThreeDimensionalTV = true",
        "sourceUsesNonnegativeProjection = true",
        "sourceSupportsNativeSparsity = true",
    ]:
        assert marker in text


def test_conditioning_acquisition_script_is_exact_artifact_scoped_and_builds_global_sparse_certificate():
    p = ROOT / "scripts/check_waller_diffusercam_conditioning.py"
    text = p.read_text()
    assert "example_psfs.mat" in text
    assert "c8516cb8f482c2bb15e75ebebd91a74b88732c95" in text
    assert "psf_bias = 102.0" in text
    assert "depth_only_same_lateral" in text
    assert "translated_column_mutual_coherence" in text
    assert "gershgorin_sparse_lower_bound" in text
    assert "max_scene_sparsity_for_positive_bound" in text
    assert "global_sparse_inverse_certificate" in text


def test_conditioning_owner_separates_executable_global_audit_from_unobserved_numeric_receipt():
    p = ROOT / "DASHI/Physics/Optics/BerkeleyDiffuserCamDepthConditioningExact.agda"
    text = p.read_text()
    assert "publishedPSFArtifactUsed = true" in text
    assert "depthOnlySameLateralAuditExecutable = true" in text
    assert "translatedColumnRestrictedAuditExecutable = true" in text
    assert "coherenceToSparseLowerBoundCompilerPaid = true" in text
    assert "depthOnlyNumericalReceiptCaptured = false" in text
    assert "translatedColumnNumericalReceiptCaptured = false" in text
    assert "globalSparseRestrictedKappaPaid = false" in text


def test_convrml_parallel_comparator_pays_same_scene_three_system_geometry_not_photon_matching_or_fzp():
    p = ROOT / "DASHI/Physics/Optics/BerkeleyConvRMLParallelComparatorExact.agda"
    text = p.read_text()
    assert "10.1364/OE.608614" in text
    assert "2602.04834" in text
    assert "0a895cb372a3c7090904027ed7c82fc0a74133c5" in text
    assert "parallelLensDiffuserRMLAcquisitionPaid = true" in text
    assert "sameSceneParallelAcquisitionPaid = true" in text
    assert "hundredThousandMeasurementsPerSystem = true" in text
    assert "matchedPhotonAcrossSystemsPaid = false" in text
    assert "fresnelZonePlateArmPaid = false" in text


def test_optics_rollup_and_acquisition_maxcut_include_global_audit_and_convrml_without_duplicate_source_owners():
    rollup = (ROOT / "DASHI/Physics/Optics/Everything.agda").read_text()
    assert "BerkeleyDiffuserCamPublicCalibrationExact" in rollup
    assert "BerkeleyDiffuserCamSourceOperatorExact" in rollup
    assert "BerkeleyDiffuserCamDepthConditioningExact" in rollup
    assert "BerkeleyConvRMLParallelComparatorExact" in rollup
    assert "WallerDiffuserCamPublicArtifactExact" not in rollup
    assert "WallerDiffuserCamCodeForwardExact" not in rollup

    maxcut = (ROOT / "DASHI/Physics/Optics/Diffraction3DImagingAcquisitionMaxCutExact.agda").read_text()
    assert "publicBerkeleyCalibrationArtifactPinned = true" in maxcut
    assert "publicBerkeleySourceOperatorPinned = true" in maxcut
    assert "depthConditioningAuditExecutable = true" in maxcut
    assert "translatedColumnRestrictedAuditExecutable = true" in maxcut
    assert "parallelLensDiffuserRMLAcquisitionPinned = true" in maxcut
    assert "berkeleyNumericPSFArrayIngested = false" in maxcut
    assert "translatedColumnNumericalReceiptCaptured = false" in maxcut
    assert "sameHRestrictedConditionNumberMeasured = false" in maxcut
    assert "matchedPhotonAcrossParallelSystems = false" in maxcut
    assert "focusedLensDiffuserFZPMatchedPhotonReceipt = false" in maxcut
