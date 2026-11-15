from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_xpollination_reconciliation_surface() -> None:
    require(
        "DASHI/Economics/AIMaxCutCrossPollinationReconciliation20261012Exact.agda",
        [
            "headlineObserverNonDescentPaid",
            "capitalBurdenRelocationPaid",
            "selectedInferenceCrackSpreadPaid",
            "cerebrasAccountingCloudMarginsPaid",
            "accountingFinancingLifeGapPaid",
            "namedExternalCashEdgesPartial",
            "providerMarginStillOpen",
            "replacementCapexStillOpen",
            "policyCausalIdentificationStillOpen",
            "exhaustiveTerminalPayerStillOpen",
        ],
    )
