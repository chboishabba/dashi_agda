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
        "stageDFourChannelProjection",
        "stageESameObjectExperiment",
        "fullNonlinearCompactEinsteinSolveStillOpen",
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
