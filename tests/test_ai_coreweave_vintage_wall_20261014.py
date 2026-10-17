from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_coreweave_vintage_wall_surface():
    text = (ROOT / "DASHI/Economics/AICoreWeaveVintageWall20261014Exact.agda").read_text(encoding="utf-8")
    for marker in [
        "coreWeaveSelectedVintageWall",
        "cumulative36MonthWindowByEnd2028Is850",
        "cumulative48MonthWindowByEnd2029Is850",
        "selectedShareBpIs5666",
        "vintageWallDoesNotCreateReplacementForecast",
    ]:
        assert marker in text
