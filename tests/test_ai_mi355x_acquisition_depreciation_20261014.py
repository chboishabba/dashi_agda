from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_mi355x_purchase_quote_depreciation_envelope():
    require("DASHI/Economics/AIMI355XAcquisitionDepreciationEnvelope20261014Exact.agda", [
        "lowEightGpuNodeQuoteUSDIs230359",
        "highEightGpuNodeQuoteUSDIs323779",
        "fiveYearLowQuoteDepreciationPerGPUThousandthUSDIs5758975",
        "fiveYearHighQuoteDepreciationPerGPUThousandthUSDIs8094475",
        "purchaseQuoteRangePaid",
        "matchedRentalNodePurchasePriceStillOpen",
        "purchaseQuoteDoesNotCreateFullOwnedTCO",
        "quoteDoesNotCreateFinancingRate",
    ])
