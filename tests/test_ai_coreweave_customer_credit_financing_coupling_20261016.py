from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_customer_credit_financing_coupling_is_explicit_and_bounded():
    text = (ROOT / "DASHI/Economics/AICoreWeaveCustomerCreditFinancingCoupling20261016Exact.agda").read_text(encoding="utf-8")
    for marker in [
        "ddtl4FundingDateCapexAdvanceBpIs9000",
        "ddtl2MarginDependsOnCustomerCredit",
        "ddtl2AvailabilityDependsOnDepreciatedGPUCostAndCustomerCredit",
        "customerCreditTransmitsIntoFinancingTerms",
        "contractBackedDebtDoesNotCreateTerminalCash",
    ]:
        assert marker in text
