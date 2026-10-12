from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_openai_payer_revenue_capacity_boundary() -> None:
    require(
        "DASHI/Economics/AIOpenAIPayerRevenueCapacity20261012Exact.agda",
        [
            "coreWeaveOpenAICommitmentMillionUSDIs6500",
            "openAIAnnualizedRevenueMillionUSDIs50000",
            "revenueScaleCapacityObserved",
            "externalCustomerCashProvenancePaidIsFalse",
            "contractRealisationPaidIsFalse",
            "revenueDoesNotCreateCashProvenance",
        ],
    )
