from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_same_instrument_2032_bond_repricing_is_paid_without_default_promotion():
    text = (ROOT / "DASHI/Economics/AICoreWeave2032BondRepricing20261016Exact.agda").read_text(encoding="utf-8")
    for marker in [
        "issueCouponTenThousandthsPercentIs9625",
        "octoberYieldLowerBoundTenThousandthsPercentIs15000",
        "yieldIncreaseLowerBoundTenThousandthsPercentIs5375",
        "sameInstrumentLongitudinalRepricingPaid",
        "secondaryYieldDoesNotCreateOccurredDefault",
    ]:
        assert marker in text
