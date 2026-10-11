from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_coreweave_reinvestment_coverage_surface() -> None:
    require(
        "DASHI/Economics/AICoreWeaveCapitalReinvestmentCoverage20261012Exact.agda",
        [
            "coreWeaveH12026ReinvestmentCoverage",
            "capexExceedsOperatingCashFlow",
            "cashFundingShortfallMillionUSD",
            "coreWeaveCashFundingShortfallIs10454",
            "replacementCapexIdentified",
            "sustainableFreeCashFlowEstablished",
        ],
    )


def test_final_reconciliation_imports_reinvestment_cut() -> None:
    require(
        "DASHI/Economics/AIMaxCutReconciliation20261012FinalExact.agda",
        [
            "AICoreWeaveCapitalReinvestmentCoverage20261012Exact",
            "coreWeaveReinvestmentCoveragePaid",
            "replacementObsolescenceStillPartial",
        ],
    )
