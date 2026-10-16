from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_covenant_compliance_cannot_recover_customer_cash_after_equity_cure():
    text = (ROOT / "DASHI/Economics/AIOpenAIContractRealisationTerminalCashNonDescent20261016Exact.agda").read_text(encoding="utf-8")
    for marker in [
        "sameCompliantCovenantObservation",
        "differentCustomerCashRealisation",
        "covenantObserverCannotDetermineTerminalCash",
        "everyRepairMustSeparateCustomerCashFromEquityCure",
    ]:
        assert marker in text
