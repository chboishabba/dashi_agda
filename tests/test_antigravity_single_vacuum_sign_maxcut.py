from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_static_and_differential_sign_obligations_are_explicit():
    text = read(
        "DASHI/Physics/Foundations/"
        "GRQFTSingleVacuumPhysicalSignMaxCutExact.agda"
    )
    for token in (
        "calibrationSquarePositive",
        "positiveSourcePromotesPositivePhysicalAmplitude",
        "zeroSourcePromotesZeroPhysicalAmplitude",
        "positiveMultiplicativePreservesPositiveDifference",
        "zeroSourceDifferenceGivesZeroPhysicalDifference",
        "zeroSourceDifferenceGivesZeroMetricModulation",
        "staticRouteNeedsPositivePromotedVacuumSign",
        "differentialRouteNeedsNonzeroSourceDifferenceForNonzeroSignal",
    ):
        assert token in text


def test_physical_promotion_frontier_imports_sign_maxcut():
    text = read(
        "DASHI/Physics/ExoticGravity/"
        "AntigravitySingleVacuumPhysicalPromotionMaxCutExact.agda"
    )
    assert "GRQFTSingleVacuumPhysicalSignMaxCutExact" in text
    assert "sourceSignAndControlMaxCutOwned" in text
