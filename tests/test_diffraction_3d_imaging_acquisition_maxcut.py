from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Physics/Optics/BerkeleyDiffuserCamPublicCalibrationExact.agda": [
        "diffuserCamCommit",
        "examplePSFBlobSHA",
        "examplePSFBytes",
        "publicCalibrationArtifactPinned",
        "numericPSFArrayIngested",
    ],
    "DASHI/Physics/Optics/BerkeleyDiffuserCamRealConditioningExecutionExact.agda": [
        "realConditioningReceiptPath",
        "realClaimScaleReceiptPath",
        "verifiedArtifactGitBlobSHA",
        "verifiedArtifactSHA256",
        "realPSFArtifactIdentityVerified = true",
        "depthOnlyNumericalReceiptCaptured = true",
        "translatedColumnNumericalReceiptCaptured = true",
        "finiteSelectedFamilyRestrictedKappaPaid = true",
        "allResolutionCameraRIPPaid = false",
    ],
    "DASHI/Physics/Optics/BerkeleyDiffuserCamSourceOperatorExact.agda": [
        "record BerkeleyDiffuserCamSourceOperatorReceipt",
        "psfBias",
        "sourceForwardUsesFFTConvolution",
        "sourceUsesDepthFlipAndShift",
        "numericOperatorMatrixMaterialised",
    ],
    "DASHI/Physics/Optics/BerkeleyDiffuserCamDepthConditioningExact.agda": [
        "conditioningAuditScript",
        "conditioningSelfTestScript",
        "claimScalePlannerScript",
        "offlineSyntheticOperatorSelfTestExecutable",
        "claimScaleMemoryPlannerExecutable",
        "sourceOperatorSelectedGridColumnCompilerPaid",
        "depthOnlySameLateralAuditExecutable",
        "translatedColumnRestrictedAuditExecutable",
        "coherenceToSparseLowerBoundCompilerPaid",
        "depthOnlyNumericalReceiptCaptured",
        "translatedColumnNumericalReceiptCaptured",
        "globalSparseRestrictedKappaPaid",
        "allResolutionCameraRIPPaid",
    ],
    "DASHI/Physics/Optics/BerkeleyLenslessInformationDesignSourceExact.agda": [
        "lenslessInfoDesignDOI",
        "lenslessInfoDesignCommit",
        "record PublishedLenslessInformationComparison",
        "parallelLenslessMeasurementsAvailable",
        "experimentalPhotonAnalysisScriptBlobSHA",
        "experimentalMeanPhotonCount = 500",
        "experimentalAnalysisBias = 10",
        "analysisPhotonNormalizationPaid = true",
        "analysisPoissonNoiseModelPaid = true",
        "physicalAcquisitionPhotonCalibrationPaid = false",
        "matchedPhysicalPhotonBudgetPaid = false",
        "focusedLensFZPComparisonPaid",
    ],
    "DASHI/Physics/Optics/BerkeleyConvRMLParallelComparatorExact.agda": [
        "convRMLDOI",
        "convRMLCommit",
        "parallelDatasetCommit",
        "parallelLensDiffuserRMLAcquisitionPaid",
        "sameSceneParallelAcquisitionPaid",
        "releasedCaptureGainZeroPaid",
        "paperVsReleasedDefaultExposureMismatchExplicit",
        "exactDatasetExposureIdentityReconciled",
        "matchedPhotonAcrossSystemsPaid",
        "fresnelZonePlateArmPaid",
    ],
    "DASHI/Physics/Optics/BerkeleyPLDExposureProvenanceCoordinateExact.agda": [
        "ExperimentalCoordinateDesignExact",
        "paperVsReleasedCollision",
        "paperAndAWBShareExposureProfile",
        "exposureProvenanceCollisionFormalised = true",
        "exactDatasetExposureProvenancePaid",
    ],
    "DASHI/Physics/Optics/Diffraction3DImagingAcquisitionMaxCutExact.agda": [
        "record Diffraction3DImagingAcquisitionMaxCut",
        "publicBerkeleyCalibrationArtifactPinned",
        "publicBerkeleySourceOperatorPinned",
        "offlineSyntheticOperatorSelfTestExecutable",
        "claimScaleMemoryPlannerExecutable",
        "sourceOperatorSelectedGridColumnCompilerPaid",
        "depthConditioningAuditExecutable",
        "translatedColumnRestrictedAuditExecutable",
        "coherenceSparseLowerBoundCompilerPaid",
        "berkeleyNumericPSFArrayIngested",
        "sameHRestrictedConditionNumberMeasured",
        "publishedInformationDesignExperimentPinned",
        "matchedAnalysisPhotonNormalizationPinned",
        "physicalAcquisitionPhotonCalibrationPinned",
        "publishedRealRMLVsDiffuserCamComparisonPinned",
        "parallelLensDiffuserRMLAcquisitionPinned",
        "exposureProvenanceCollisionFormalised",
        "parallelExposureProvenanceReconciled",
        "matchedPhotonAcrossParallelSystems",
        "focusedLensDiffuserFZPMatchedPhotonReceipt",
    ],
}


def test_acquisition_owners_exist_with_pinned_source_markers():
    for rel, markers in REQUIRED.items():
        path = ROOT / rel
        assert path.exists(), f"missing acquisition owner: {rel}"
        text = path.read_text(encoding="utf-8")
        for marker in markers:
            assert marker in text, f"{rel} missing marker {marker!r}"


def test_public_diffusercam_artifact_identity_is_exactly_pinned():
    text = (ROOT / "DASHI/Physics/Optics/BerkeleyDiffuserCamPublicCalibrationExact.agda").read_text(encoding="utf-8")
    assert "c8516cb8f482c2bb15e75ebebd91a74b88732c95" in text
    assert "db59065bdaf44fe771a6d3fbe22ae3c703527b5f" in text
    assert "10823885" in text
    assert "example_data/example_psfs.mat" in text


def test_public_information_design_source_is_exactly_pinned_and_analysis_photons_are_not_physical_calibration():
    text = (ROOT / "DASHI/Physics/Optics/BerkeleyLenslessInformationDesignSourceExact.agda").read_text(encoding="utf-8")
    assert "10.1364/OPTICA.570334" in text
    assert "2506.08513" in text
    assert "f26873c2b58b82d84353bab2bf6edd478c5892a8" in text
    assert "dc8af843841870d714ccd70f0d689eaeee34d788" in text
    assert "full_dataset / np.mean(full_dataset)" in text
    assert "analysisPhotonNormalizationPaid = true" in text
    assert "physicalAcquisitionPhotonCalibrationPaid = false" in text
    assert "matchedPhysicalPhotonBudgetPaid = false" in text


def test_convrml_same_scene_parallel_comparator_is_pinned_but_photon_and_fzp_claims_stay_open():
    text = (ROOT / "DASHI/Physics/Optics/BerkeleyConvRMLParallelComparatorExact.agda").read_text(encoding="utf-8")
    assert "10.1364/OE.608614" in text
    assert "2602.04834" in text
    assert "0a895cb372a3c7090904027ed7c82fc0a74133c5" in text
    assert "55cca430641ad785bd7bc355fb0f00671c0d7441" in text
    assert "parallelLensDiffuserRMLAcquisitionPaid = true" in text
    assert "matchedPhotonAcrossSystemsPaid = false" in text
    assert "fresnelZonePlateArmPaid = false" in text


def test_acquisition_maxcut_closes_real_psf_execution_but_keeps_physical_comparison_leaves_open():
    text = (ROOT / "DASHI/Physics/Optics/Diffraction3DImagingAcquisitionMaxCutExact.agda").read_text(encoding="utf-8")
    assert "offlineSyntheticOperatorSelfTestExecutable = true" in text
    assert "claimScaleMemoryPlannerExecutable = true" in text
    assert "berkeleyNumericPSFArrayIngested = RealConditioning.realPSFArtifactIdentityVerified" in text
    assert "depthOnlyNumericalReceiptCaptured = Conditioning.depthOnlyNumericalReceiptCaptured" in text
    assert "translatedColumnNumericalReceiptCaptured = Conditioning.translatedColumnNumericalReceiptCaptured" in text
    assert "sameHRestrictedConditionNumberMeasured = Conditioning.globalSparseRestrictedKappaPaid" in text
    assert "matchedAnalysisPhotonNormalizationPinned = true" in text
    assert "physicalAcquisitionPhotonCalibrationPinned = InfoSource.physicalAcquisitionPhotonCalibrationPaid" in text
    assert "exposureProvenanceCollisionFormalised = true" in text
    assert "parallelExposureProvenanceReconciled = ExposureProvenance.exactDatasetExposureProvenancePaid" in text
    assert "matchedPhotonAcrossParallelSystems = false" in text
    assert "focusedLensDiffuserFZPMatchedPhotonReceipt = false" in text
    assert "publicBerkeleyCalibrationArtifactPinned = true" in text
    assert "publicBerkeleySourceOperatorPinned = true" in text
    assert "sourceOperatorSelectedGridColumnCompilerPaid = true" in text
    assert "depthConditioningAuditExecutable = true" in text
    assert "translatedColumnRestrictedAuditExecutable = true" in text
    assert "publishedInformationDesignExperimentPinned = true" in text
    assert "publishedRealRMLVsDiffuserCamComparisonPinned = true" in text
    assert "parallelLensDiffuserRMLAcquisitionPinned = true" in text


def test_rollup_exports_acquisition_maxcut_and_real_execution_owner():
    text = (ROOT / "DASHI/Physics/Optics/Everything.agda").read_text(encoding="utf-8")
    for owner in (
        "BerkeleyDiffuserCamPublicCalibrationExact",
        "BerkeleyDiffuserCamSourceOperatorExact",
        "BerkeleyDiffuserCamRealConditioningExecutionExact",
        "BerkeleyDiffuserCamDepthConditioningExact",
        "BerkeleyLenslessInformationDesignSourceExact",
        "BerkeleyConvRMLParallelComparatorExact",
        "BerkeleyPLDExposureProvenanceCoordinateExact",
        "Diffraction3DImagingAcquisitionMaxCutExact",
    ):
        assert owner in text
