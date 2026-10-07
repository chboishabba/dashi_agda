from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    p = ROOT / rel
    assert p.is_file(), f"missing {rel}"
    return p.read_text(encoding="utf-8", errors="replace")


def test_positive_g_weak_field_metric_owner_exists():
    text = read("DASHI/Physics/Foundations/PositiveGActiveStressWeakFieldMetricExact.agda")
    for token in (
        "activeSourceDensity",
        "interiorPotential",
        "exteriorPotential",
        "surfacePotentialContinuous",
        "surfaceDerivativeContinuous",
        "negativeActiveSourceGivesOutwardInteriorAcceleration",
        "negativeActiveMassGivesOutwardExteriorAcceleration",
    ):
        assert token in text


def test_anisotropic_TOV_conservation_obstruction_is_explicit():
    text = read("DASHI/Physics/Foundations/PositiveGAnisotropicTOVConservationExact.agda")
    for token in (
        "anisotropicConservationResidual",
        "boundaryConstantPressureRequiresPhiPrimeMinusTwo",
        "weakFieldBoundaryResidualIsFiveThirds",
        "currentTwoZoneFixtureIsNotFullConservedStaticSolution",
    ):
        assert token in text


def test_conserved_profile_compiler_eliminates_tangential_pressure_unknown():
    text = read("DASHI/Physics/Foundations/PositiveGConservedAnisotropicProfileCompilerExact.agda")
    for token in (
        "tangentialPressureFromConservation",
        "conservationResidualFactorization",
        "activeSourceAfterConservationCompiler",
        "tangentialPressureNoLongerIndependentUnknown",
    ):
        assert token in text


def test_strongest_existing_nonlinear_repulsive_geometry_is_consumed():
    terminal = read("DASHI/Physics/ExoticGravity/AntigravityABCDETerminalMaxCutExact.agda")
    for token in (
        "stageCIsraelBranchMaxCut",
        "stageCNambuGotoRepulsiveBubbleBoundary",
        "stageCSourceNativeNambuConditionalBoundary",
        "selectedNonlinearRepulsiveExteriorGeometryConstructed",
        "sourceNativeVacuumReadoutStillOpen",
        "sourceNativePinnedStressWeldStillOpen",
    ):
        assert token in terminal

    bubble = read("DASHI/Physics/Foundations/GRQFTNambuGotoRepulsiveBubbleMaxCutExact.agda")
    for token in (
        "positiveMetricMass",
        "positiveNewtonGCompatible",
        "outwardExteriorAcceleration",
        "nambuGotoEquationOfState",
        "necWecDecCompatible",
        "sourceNativeCMP119PotentialCouplingDerived",
    ):
        assert token in bubble


def test_device_observable_compiler_covers_weight_freefall_clock_optical():
    text = read("DASHI/Physics/ExoticGravity/AntigravityDeviceMetricObservableCompilerExact.agda")
    for token in (
        "freeFallPrediction",
        "supportWeightPrediction",
        "clockFractionalShiftPrediction",
        "opticalMetricPrediction",
        "sameMetricAcrossAllFourChannels",
    ):
        assert token in text


def test_A_to_E_terminal_owner_exists_and_is_fail_closed():
    text = read("DASHI/Physics/ExoticGravity/AntigravityABCDETerminalMaxCutExact.agda")
    for token in (
        "stageASourceContract",
        "stageBActiveStressCriterion",
        "stageCWeakFieldMetricSolve",
        "stageCNonlinearConservationAudit",
        "stageCConservedProfileCompiler",
        "stageCSphericalExteriorMassObstruction",
        "stageCLocalRepulsiveInteriorFamily",
        "stageDFourChannelProjection",
        "stageESameObjectExperiment",
        "physicalDeviceStressRealisationStillOpen",
    ):
        assert token in text


def test_everything_imports_A_to_E_modules():
    text = read("DASHI/Physics/ExoticGravity/Everything.agda")
    for module in (
        "DASHI.Physics.ExoticGravity.AntigravityDeviceMetricObservableCompilerExact",
        "DASHI.Physics.ExoticGravity.AntigravityABCDETerminalMaxCutExact",
    ):
        assert f"import {module}" in text
