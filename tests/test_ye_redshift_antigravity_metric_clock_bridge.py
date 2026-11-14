from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DASHI = REPO_ROOT / "DASHI"
MODULE = DASHI / "Physics" / "Closure" / "BothwellYe2022AntigravityMetricClockBridgeExact.agda"
STATUS = DASHI / "Physics" / "Closure" / "QuantumClockEmpiricalRedshiftIngestionStatusExact.agda"
ROLLUP = DASHI / "Physics" / "Closure" / "YeRedshiftEverything.agda"


def read(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(REPO_ROOT)}"
    return path.read_text(encoding="utf-8")


def test_bridge_reuses_existing_clock_and_antigravity_owners() -> None:
    text = read(MODULE)
    for marker in (
        "canonicalBothwellYe2022ChronometricGeodesyBridge",
        "canonicalBothwellYe2022RedshiftComparison",
        "canonicalConsumerScopedCalibrationBoundary",
        "metricClockDiscriminator",
        "engineeredMetricResponse",
    ):
        assert marker in text


def test_standard_clock_reference_does_not_promote_antigravity() -> None:
    text = read(MODULE)
    for marker in (
        "standardMetricClockReferenceConstructed = true",
        "standardGRRedshiftComparisonAvailable = true",
        "antigravityMetricClockConsumerAdequacyConstructed = false",
        "engineeredMetricResponseObserved = false",
        "negativeGInferred = false",
        "antigravityMechanismValidated = false",
        "antigravityPromotionAllowed = false",
    ):
        assert marker in text


def test_bridge_is_a_reference_and_negative_control_surface() -> None:
    text = read(MODULE)
    for marker in (
        "ordinaryGravityClockReferenceForExoticComparison = true",
        "sameObjectExoticInterventionEvidencePresent = false",
        "The Bothwell/Ye clock supplies a standard-gravity metric/clock reference coordinate",
        "It does not observe an engineered metric response, negative G, sign-reversed gravity, or an antigravity mechanism",
    ):
        assert marker in text


def test_status_and_rollup_register_bridge_without_opening_gates() -> None:
    status = read(STATUS)
    for marker in (
        "antigravityMetricClockBridgeConstructed = true",
        "antigravityMetricClockPromotionAllowed = false",
        "terminalSIMetrologyPromotionAllowed = false",
    ):
        assert marker in status

    rollup = read(ROLLUP)
    line = "import DASHI.Physics.Closure.BothwellYe2022AntigravityMetricClockBridgeExact"
    assert rollup.count(line) == 1
