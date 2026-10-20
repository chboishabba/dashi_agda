from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_selected_inference_crack_spread_surface() -> None:
    require(
        "DASHI/Economics/AISelectedInferenceCrackSpread20261012Exact.agda",
        [
            "selectedHostingSpreadCentsIs27",
            "selectedHostingSpreadShareBpIs2250",
            "buyerSubstitutionSpreadPaid",
            "providerMarginStillOpen",
            "selectedCrackSpreadDoesNotCreateProviderMargin",
        ],
    )
