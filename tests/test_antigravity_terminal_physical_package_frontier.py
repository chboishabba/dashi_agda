from pathlib import Path

MODULE = Path("DASHI/Physics/ExoticGravity/AntigravityTerminalPhysicalPackageFrontierExact.agda")


def test_terminal_frontier_counts_packages_not_adapter_debt():
    text = MODULE.read_text()
    required = [
        "typedLocalCTerminalPhysicalPackageStillRequired = true",
        "commonGravityCalibrationPackageStillRequired = true",
        "matchedExperimentPackageStillRequired = true",
        "ttDevicePackageRequiredForStaticOrScalarDifferentialRoute = false",
        "ttDevicePackageRequiredWhenPropagatingGWRouteSelected = true",
        "independentStaticMetricResponseTheoremStillRequired = false",
        "independentDifferentialSameObjectTheoremStillRequired = false",
        "r109SignMachineryRequiredForResponseReuse = false",
        "representationOnlyAdapterDebtRemains = false",
        "mandatoryStaticResponsePhysicalPackageCount = 3",
        "mandatoryScalarDifferentialPhysicalPackageCount = 3",
        "mandatoryPropagatingGWPhysicalPackageCount = 4",
    ]
    for needle in required:
        assert needle in text
