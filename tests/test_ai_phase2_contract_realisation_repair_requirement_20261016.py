from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_phase2_requires_customer_cash_equity_cure_separation():
    text = (ROOT / "DASHI/Economics/AICapitalPhase2Acquisition20261016Exact.agda").read_text(encoding="utf-8")
    for marker in [
        "contractRealisationEquityCureMechanismPaid",
        "covenantComplianceInsufficientForCustomerCashPaid",
        "realisedCustomerCashVsCureDecompositionPaidIsFalse",
    ]:
        assert marker in text
