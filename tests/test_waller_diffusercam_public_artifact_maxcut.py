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


def test_conditioning_acquisition_script_is_exact_artifact_scoped_and_builds_same_source_h_sparse_certificate():
    p = ROOT / "scripts/check_waller_diffusercam_conditioning.py"
    text = p.read_text()
    assert "example_psfs.mat" in text
    assert "c8516cb8f482c2bb15e75ebebd91a74b88732c95" in text
    assert "psf_bias = 102.0" in text
    assert "depth_only_same_lateral" in text
    assert "source_forward_selected_columns" in text
    assert "padded_circular_convolution_crop" in text
    assert "translated_column_mutual_coherence" in text
    assert "gershgorin_sparse_lower_bound" in text
    assert "max_scene_sparsity_for_positive_bound" in text
    assert "global_sparse_inverse_certificate" in text
    assert "certificate_scope" in text


def test_real_conditioning_owner_records_verified_execution_and_preserves_scope_boundary():
    p = ROOT / "DASHI/Physics/Optics/BerkeleyDiffuserCamRealConditioningExecutionExact.agda"
    text = p.read_text()
    assert "db59065bdaf44fe771a6d3fbe22ae3c703527b5f" in text
    assert "fdbc8b2c7a8753f146e1b270a3f0ae2d0f70cb2c4ff49aef4a926670c0f7c906" in text
    assert "verifiedArtifactBytes = 10823885" in text
    assert "numericalRank = 44" in text
    assert "selectedColumnCount = 396" in text
    assert "maxSceneSparsityPositiveBound = 1" in text
    assert "depthOnlyNumericalReceiptCaptured = true" in text
    assert "translatedColumnNumericalReceiptCaptured = true" in text
    assert "finiteSelectedFamilyRestrictedKappaPaid = true" in text
    assert "allResolutionCameraRIPPaid = false" in text
    assert "matchedPhotonComparisonPaid = false" in text


def test_conditioning_owner_consumes_real_receipt_without_promoting_all_resolution_rip():
    p = ROOT / "DASHI/Physics/Optics/BerkeleyDiffuserCamDepthConditioningExact.agda"
    text = p.read_text()
    assert "publishedPSFArtifactUsed = true" in text
    assert "depthOnlySameLateralAuditExecutable = true" in text
    assert "sourceOperatorSelectedGridColumnCompilerPaid = true" in text
    assert "translatedColumnRestrictedAuditExecutable = true" in text
    assert "coherenceToSparseLowerBoundCompilerPaid = true" in text
    assert "depthOnlyNumericalReceiptCaptured = RealExecution.depthOnlyNumericalReceiptCaptured" in text
    assert "translatedColumnNumericalReceiptCaptured = RealExecution.translatedColumnNumericalReceiptCaptured" in text
    assert "globalSparseRestrictedKappaPaid = RealExecution.finiteSelectedFamilyRestrictedKappaPaid" in text
    assert "allResolutionCameraRIPPaid = RealExecution.allResolutionCameraRIPPaid" in text


def test_convrml_parallel_comparator_pays_hardware_capture_coordinates_and_preserves_exposure_provenance_mismatch():
    p = ROOT / "DASHI/Physics/Optics/BerkeleyConvRMLParallelComparatorExact.agda"
    text = p.read_text()
    assert "10.1364/OE.608614" in text
    assert "2602.04834" in text
    assert "0a895cb372a3c7090904027ed7c82fc0a74133c5" in text
    assert "55cca430641ad785bd7bc355fb0f00671c0d7441" in text
    assert "parallelLensDiffuserRMLAcquisitionPaid = true" in text
    assert "sameSceneParallelAcquisitionPaid = true" in text
    assert "hundredThousandMeasurementsPerSystem = true" in text
    assert "identicalSensorModelPaid = true" in text
    assert "sameIlluminationPaid = true" in text
    assert "sameMagnificationPaid = true" in text
    assert "exposureCalibrationPaid = true" in text
    assert "rmlExposureMilliseconds = 80" in text
    assert "diffuserExposureMilliseconds = 50" in text
    assert "lensExposureMilliseconds = 4" in text
    assert "releasedDiffuserExposureMicroseconds = 25000" in text
    assert "releasedRMLExposureMicroseconds = 80000" in text
    assert "releasedGroundTruthExposureMicroseconds = 18000" in text
    assert "releasedCaptureGainZeroPaid = true" in text
    assert "releasedCaptureRGB8Paid = true" in text
    assert "paperVsReleasedDefaultExposureMismatchExplicit = true" in text
    assert "exactDatasetExposureIdentityReconciled = false" in text
    assert "equalExposureAcrossSystemsPaid = false" in text
    assert "matchedPhotonAcrossSystemsPaid = false" in text
    assert "fresnelZonePlateArmPaid = false" in text


def test_pld_exposure_provenance_collision_reuses_experimental_coordinate_design():
    p = ROOT / "DASHI/Physics/Optics/BerkeleyPLDExposureProvenanceCoordinateExact.agda"
    text = p.read_text()
    assert "ExperimentalCoordinateDesignExact" in text
    assert "paper100k" in text
    assert "releasedCurrent100k" in text
    assert "earlierAWB25k" in text
    assert "paperVsReleasedCollision" in text
    assert "paperAndAWBShareExposureProfile" in text
    assert "exposureProfileDoesNotIdentifyDataset = true" in text
    assert "exactDatasetExposureProvenancePaid = false" in text


def test_optics_rollup_and_acquisition_maxcut_include_real_execution_without_duplicate_source_owners():
    rollup = (ROOT / "DASHI/Physics/Optics/Everything.agda").read_text()
    assert "BerkeleyDiffuserCamPublicCalibrationExact" in rollup
    assert "BerkeleyDiffuserCamSourceOperatorExact" in rollup
    assert "BerkeleyDiffuserCamRealConditioningExecutionExact" in rollup
    assert "BerkeleyDiffuserCamDepthConditioningExact" in rollup
    assert "BerkeleyConvRMLParallelComparatorExact" in rollup
    assert "BerkeleyPLDExposureProvenanceCoordinateExact" in rollup
    assert "WallerDiffuserCamPublicArtifactExact" not in rollup
    assert "WallerDiffuserCamCodeForwardExact" not in rollup

    maxcut = (ROOT / "DASHI/Physics/Optics/Diffraction3DImagingAcquisitionMaxCutExact.agda").read_text()
    assert "publicBerkeleyCalibrationArtifactPinned = true" in maxcut
    assert "publicBerkeleySourceOperatorPinned = true" in maxcut
    assert "sourceOperatorSelectedGridColumnCompilerPaid = true" in maxcut
    assert "depthConditioningAuditExecutable = true" in maxcut
    assert "translatedColumnRestrictedAuditExecutable = true" in maxcut
    assert "parallelLensDiffuserRMLAcquisitionPinned = true" in maxcut
    assert "parallelSensorIlluminationGeometryPinned = true" in maxcut
    assert "parallelExposureCalibrationPinned = true" in maxcut
    assert "releasedCaptureGainAndFormatPinned = true" in maxcut
    assert "exposureProvenanceCollisionFormalised = true" in maxcut
    assert "parallelExposureProvenanceReconciled = ExposureProvenance.exactDatasetExposureProvenancePaid" in maxcut
    assert "berkeleyNumericPSFArrayIngested = RealConditioning.realPSFArtifactIdentityVerified" in maxcut
    assert "translatedColumnNumericalReceiptCaptured = Conditioning.translatedColumnNumericalReceiptCaptured" in maxcut
    assert "sameHRestrictedConditionNumberMeasured = Conditioning.globalSparseRestrictedKappaPaid" in maxcut
    assert "matchedPhotonAcrossParallelSystems = false" in maxcut
    assert "focusedLensDiffuserFZPMatchedPhotonReceipt = false" in maxcut
