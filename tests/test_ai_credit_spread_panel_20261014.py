from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_ai_credit_spread_differential_surface():
    require("DASHI/Economics/AICreditSpreadDifferential20261014Exact.agda", [
        "aiLinkedAverageSpreadBpIs115",
        "broaderIGAverageSpreadBpIs78",
        "spreadPremiumBpIs37",
        "spreadPremiumDoesNotCreateDefault",
        "spreadPremiumDoesNotCreateBubble",
    ])
