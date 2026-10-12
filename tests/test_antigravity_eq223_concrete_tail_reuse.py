from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_preferred_r136_route_reuses_concrete_r109_tail_compiler():
    text = read(
        "DASHI/Physics/Foundations/"
        "CMP119AntigravityEq223ConcreteTailReuseMaxCutExact.agda"
    )
    for token in (
        "preferredConcreteTailRouteEliminatesExactFiniteContinuumEquality",
        "pinnedExpectationEqualsDGammaStillRequired",
        "concreteSameSequenceTailBoundStillRequired",
        "strictFinitePlusTailMarginStillRequired",
        "legacyDirectResponseEqualityStillAvailableButNotShortestPath",
    ):
        assert token in text


def test_post_normalization_scheduler_uses_concrete_tail_r136_recut():
    text = read(
        "DASHI/Physics/ExoticGravity/AntigravityPostNormalizationMaxCutExact.agda"
    )
    assert "CMP119AntigravityEq223ConcreteTailReuseMaxCutExact" in text
    assert "continuumExactFiniteEqualsR136RequiredOnPreferredRoute" in text
    assert "continuumPinnedFiniteAnchorAndTailBoundStillRequired" in text
