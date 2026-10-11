from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_coreweave_sign_only_capital_spread_surface() -> None:
    require(
        "DASHI/Economics/AICoreWeaveCapitalSpreadSign20261012Exact.agda",
        [
            "coreWeaveOperatingLossObserved",
            "coreWeaveDebtPrincipalPositive",
            "coreWeaveDebtRatePositive",
            "standardWACCSignConditions",
            "coreWeaveROICSignNegative",
            "coreWeaveWACCSignPositive",
            "coreWeaveCapitalSpreadSignNegative",
            "numericROICStillOpen",
            "numericWACCStillOpen",
        ],
    )


def test_final_reconciliation_imports_sign_cut() -> None:
    require(
        "DASHI/Economics/AIMaxCutReconciliation20261012FinalExact.agda",
        [
            "AICoreWeaveCapitalSpreadSign20261012Exact",
            "coreWeaveCapitalSpreadSignPaid",
            "numericROICWACCStillOpen",
        ],
    )
