from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_coreweave_contribution_margin_expectation_surface() -> None:
    require(
        "DASHI/Economics/AICoreWeaveContributionMarginExpectation20261012Exact.agda",
        [
            "expectedContributionMarginImprovementLowerPtIs5",
            "expectedContributionMarginImprovementUpperPtIs10",
            "expectedRelativeContributionMarginImprovementIs25Percent",
            "julyPriceIncreaseAcrossSKUsIs70Percent",
            "realisedContributionMarginPaidIsFalse",
            "providerMarginalServingCostPaidIsFalse",
            "expectedMarginDoesNotCreateRealisedMargin",
        ],
    )
