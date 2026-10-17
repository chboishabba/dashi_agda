from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_historical_named_microsoft_revenue_does_not_deanonymise_2026():
    text = (ROOT / "DASHI/Economics/AICoreWeaveMicrosoftHistoricalRevenue20261016Exact.agda").read_text(encoding="utf-8")
    for marker in [
        "annualRevenueMillionUSDIs5131",
        "microsoftRevenueSharePercentIs67",
        "microsoftRecognisedRevenueMillionUSDApproxIs3438",
        "historicalNamedRevenuePaid",
        "namedRevenueDoesNotCreateNamedCash",
        "historicalMicrosoftDoesNotIdentify2026CustomerA",
    ]:
        assert marker in text
