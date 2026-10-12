from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_equal_index_open_closed_pair_surface() -> None:
    require(
        "DASHI/Economics/AIEqualIndexOpenClosedSpread20261012Exact.agda",
        [
            "bothIntelligenceIndex46",
            "costPerTaskClosedOpenRatioAbove6x",
            "blendedTokenPriceClosedOpenRatioAbove43x",
            "sameAggregateIndexPaid",
            "sameCapabilityVectorPaidIsFalse",
            "equalScalarIndexDoesNotCreateCapabilityIdentity",
        ],
    )
