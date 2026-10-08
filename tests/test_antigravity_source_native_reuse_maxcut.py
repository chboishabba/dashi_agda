from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_localized_vacuum_readout_reuses_existing_projector():
    text = read("DASHI/Physics/Foundations/CMP119AntigravityLocalizedVacuumReadoutExact.agda")
    for token in (
        "localizedVacuumReadout",
        "plaquetteCoefficientProjector",
        "sourceNativeAmplitudeReceiptFromProjectedVacua",
        "independentVacuumReadoutStillRequired",
        "twoSourceAmplitudeEqualitiesStillRequired",
    ):
        assert token in text


def test_eq223_metric_stress_route_bypasses_old_ancestry_adapter():
    text = read("DASHI/Physics/Foundations/CMP119AntigravityEq223MetricStressReuseMaxCutExact.agda")
    for token in (
        "sourceCompleteFiniteMetricVariation",
        "vacuumVariationIsLiteralEq223V",
        "sameObjectEffectiveActionResponse",
        "oldPinnedStressAncestryAdapterRequiredOnPreferredRoute",
        "directResponseEqualityStillRequired",
    ):
        assert token in text


def test_terminal_owner_compresses_remaining_source_frontier():
    text = read("DASHI/Physics/ExoticGravity/AntigravitySourceNativeReuseTerminalExact.agda")
    for token in (
        "canonicalLocalizedVacuumReadoutBoundary",
        "canonicalEq223MetricStressReuseBoundary",
        "rationalVacuumReadoutIsNoLongerIndependentLeaf",
        "oldPinnedStressAncestryAuthorityIsNoLongerPreferredLeaf",
        "actualTwoSourceAmplitudeValuesStillOpen",
        "actualR136EffectiveActionResponseEqualityStillOpen",
    ):
        assert token in text
