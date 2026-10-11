from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_final_reconciliation_surface() -> None:
    require(
        "DASHI/Economics/AIMaxCutReconciliation20261012FinalExact.agda",
        [
            "selectedPublicEquityDynamicsPaid",
            "vercelOpenWeightTrajectoryPaid",
            "selectedBenchmarkPricePairPaid",
            "coreWeaveTwoSidedConcentrationPaid",
            "coreWeaveDebtCostSurfacePaid",
            "wholeComplexMarketDynamicsStillPartial",
            "globalOpenWeightTrajectoryStillOpen",
            "sameCapabilityScarcityRentStillOpen",
            "providerServingMarginStillOpen",
            "terminalPayerStillOpen",
            "realisedROICWACCStillOpen",
        ],
    )


def test_new_scoped_owners_exist() -> None:
    require(
        "DASHI/Economics/AIFixedBasketMarketSeries20261012Exact.agda",
        ["selectedAICapitalBasketResult", "selectedFlipRateIsClosed", "globalVolatilityStillOpen"],
    )
    require(
        "DASHI/Economics/AIOpenWeightTrajectory20261012Exact.agda",
        ["vercelOpenWeightTrajectory", "platformPersistenceIsObserved", "globalTrajectoryStillOpen"],
    )
    require(
        "DASHI/Economics/AIQualityNormalizedPriceSpread20261012Exact.agda",
        ["mimoVsOpusBenchmarkPricePair", "selectedPairIsPaid", "providerMarginStillOpen"],
    )
    require(
        "DASHI/Economics/AITwoSidedConcentrationPropagation20261012Exact.agda",
        ["coreWeaveTwoSidedConcentration", "coreScientificDependencyIs7700bp", "terminalIndependenceStillOpen"],
    )
    require(
        "DASHI/Economics/AICoreWeaveDebtCostBoundary20261012Exact.agda",
        ["coreWeaveDebtCostBoundary", "debtSurfaceIsPaid", "waccStillOpen", "capitalSpreadStillOpen"],
    )


def test_rollup_wires_final_reconciliation() -> None:
    require(
        "DASHI/Economics/AIEntanglementEverything2026.agda",
        [
            "AIFixedBasketMarketSeries20261012Exact",
            "AIOpenWeightTrajectory20261012Exact",
            "AIQualityNormalizedPriceSpread20261012Exact",
            "AITwoSidedConcentrationPropagation20261012Exact",
            "AICoreWeaveDebtCostBoundary20261012Exact",
            "AIMaxCutReconciliation20261012FinalExact",
        ],
    )
