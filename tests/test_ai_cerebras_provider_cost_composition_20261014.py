from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_cerebras_provider_cost_composition():
    require("DASHI/Economics/AICerebrasProviderCostComposition20261014Exact.agda", [
        "q1CloudCostMillionThousandUSDIs42299",
        "q1CloudCostIncreaseThousandUSDIs32801",
        "q1DataCenterIncreaseInclDepreciationThousandUSDIs28800",
        "q1PassThroughIncreaseThousandUSDIs4000",
        "q2CloudCostThousandUSDIs101410",
        "providerSegmentCostCompositionPaid",
        "segmentCostDoesNotCreateMarginalTokenCost",
    ])
