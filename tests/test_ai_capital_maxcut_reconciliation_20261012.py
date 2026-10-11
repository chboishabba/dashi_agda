from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_terminal_reconciliation_surface() -> None:
    require(
        "DASHI/Economics/AIMaxCutReconciliation20261012Exact.agda",
        [
            "coreWeaveEntityRolloverPaid",
            "entityPersistencePaid",
            "globalPersistenceStillOpen",
            "cerebrasRoleOverlapPaid",
            "terminalPayerIndependenceStillOpen",
            "infrastructureCommitmentTrajectoryPaid",
            "realisedROICWACCStillOpen",
            "qualityAdjustedInferenceMarginStillOpen",
            "openWeightPlatformPointPaid",
            "selectedFixedBasketMarketSeriesPaid",
            "globalMarketDynamicsStillPartial",
            "selectedBasketFlipRateNowPaid",
            "selectedBasketVolatilityNowPaid",
            "selectedBasketStillNotGlobalFlipRate",
            "selectedBasketStillNotGlobalVolatility",
            "regulatoryMeasuredBurdenStillOpen",
            "globalStateStillNonPromotable",
        ],
    )


def test_fresh_market_owners_are_wired() -> None:
    require(
        "DASHI/Economics/AIMarketOpenWeightFreshAcquisition20261012Exact.agda",
        ["vercelOpenWeightSnapshot20261010", "openWeightPointIs6130bp", "fixedBasketStillUnclosed"],
    )
    require(
        "DASHI/Economics/AIFixedBasketMarketSeries20261012Exact.agda",
        ["selectedAICapitalBasket", "selectedAICapitalBasketResult", "selectedFlipRateIsClosed", "globalVolatilityStillOpen"],
    )
    require(
        "DASHI/Economics/AIEntanglementEverything2026.agda",
        ["AIMarketOpenWeightFreshAcquisition20261012Exact", "AIFixedBasketMarketSeries20261012Exact", "AIMaxCutReconciliation20261012Exact"],
    )


def test_rollups_import_terminal_reconciliation() -> None:
    require(
        "DASHI/Economics/AIEntanglementEverything2026.agda",
        ["AIMaxCutReconciliation20261012Exact"],
    )
    require(
        "DASHI/Economics/Everything.agda",
        ["AIMaxCutReconciliation20261012Exact"],
    )
