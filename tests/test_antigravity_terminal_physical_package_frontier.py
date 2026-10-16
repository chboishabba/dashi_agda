from pathlib import Path

MODULE = Path("DASHI/Physics/ExoticGravity/AntigravityTerminalPhysicalPackageFrontierExact.agda")


def test_terminal_frontier_counts_packages_not_adapter_debt():
    text = MODULE.read_text()
    for needle in (
        "typedLocalCTerminalPhysicalPackageStillRequired",
        "preferredSharedWightmanTerminalAvailable",
        "independentPinnedBoostTraceSplitRequired",
        "commonGravityCalibrationPackageStillRequired",
        "matchedExperimentPackageStillRequired",
        "ttDevicePackageRequiredForStaticOrScalarDifferentialRoute",
        "ttDevicePackageRequiredWhenPropagatingGWRouteSelected",
        "independentStaticMetricResponseTheoremStillRequired",
        "independentDifferentialSameObjectTheoremStillRequired",
        "r109SignMachineryRequiredForResponseReuse",
        "representationOnlyAdapterDebtRemains",
        "mandatoryStaticResponsePhysicalPackageCount = 3",
        "mandatoryScalarDifferentialPhysicalPackageCount = 3",
        "mandatoryPropagatingGWPhysicalPackageCount = 4",
    ):
        assert needle in text


def test_measured_g_is_paid_but_scale_product_remains_inside_calibration_package():
    text = MODULE.read_text()
    for needle in (
        "acceptedMeasuredGAuthorityStillOpen",
        "stressLengthSquaredScaleStillOpen",
        "acceptedMeasuredGAuthorityPaid",
        "SI.acceptedMeasuredGAuthorityStillRequired",
        "SI.sourceStressLengthSquaredScaleStillRequired",
        "acceptedMeasuredGAuthorityStillOpenIsFalse",
    ):
        assert needle in text


def test_p1_is_q1_plus_a2_semantics_not_retired_e24_presentation_data():
    text = MODULE.read_text()
    for needle in (
        "AntigravityP1MarkedOSParetoReuseMaxCutExact as P1",
        "p1OpaqueAnalyticEstimateCount",
        "p1RemainingSameObjectResidualCount",
        "p1Q1PathDerivativeSemanticsAndEquivarianceStillRequired",
        "p1PrimitiveE1DerivativeEquivarianceProjectRequired = false",
        "p1E24ObservableAndTwoAdmissibilityProofsStillRequired = false",
        "p1E24SelectedObservableChoiceStillRequired = false",
        "p1E24PositiveTimeAdmissibilityStillRequired = false",
        "p1E24GaugeInvariantAdmissibilityStillRequired = false",
        "p1E24PairToCanonicalObservableSemanticsStillRequired = true",
        "p1E24ArbitraryMeaningPredicateRequired = false",
        "p1AllStressCylinderEncodingRequired = false",
        "p1IndependentE4StressSelectionRequired = false",
        "p1IndependentE4DecayEstimateRequired = false",
        "p1IndependentTerminalLawProjectsRequired = false",
    ):
        assert needle in text


def test_p3_compiler_structure_is_paid_but_physical_experiment_remains_open():
    text = MODULE.read_text()
    for needle in (
        "AntigravitySameStateFourChannelDiscriminatorExact as FourChannel",
        "sameStateFourChannelCompilerConstructed",
        "sameSourceStressMetricChainConstructed",
        "mechanismSignatureTemplatesConstructed",
        "candidateBoundNuisanceClosureContractConstructed",
        "preferredSingleVacuumFixtureFeedsDiscriminator",
        "physicalMatchedSourceSwitchStillOpen",
        "numericalSystematicsBudgetStillOpen",
        "empiricalReplicationStillOpen",
        "fourChannelStructureDoesNotPayExperiment",
    ):
        assert needle in text
