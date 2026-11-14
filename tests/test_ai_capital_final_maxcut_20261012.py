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
            "sameModelSelfHostEngineeringCostPaid",
            "headlineObserverNonDescentPaid",
            "coreWeaveTwoSidedConcentrationPaid",
            "coreWeaveDebtCostSurfacePaid",
            "coreWeaveCapitalSpreadSignPaid",
            "coreWeaveReinvestmentCoveragePaid",
            "coreWeaveCapexNonidentifiabilityPaid",
            "coreWeaveAccountingLifePaid",
            "coreWeaveNamedPayerCapacityPaid",
            "coreWeaveNamedPayerSaturationPaid",
            "terminalPayerConsumerIndexingPaid",
            "terminalPayerStillPartial",
            "replacementObsolescenceStillPartial",
            "policyCausalAdmissionStillPartial",
            "wholeComplexMarketDynamicsStillPartial",
            "globalOpenWeightTrajectoryStillOpen",
            "sameCapabilityScarcityRentStillOpen",
            "providerServingMarginStillPartial",
            "numericROICWACCStillOpen",
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
    require(
        "DASHI/Economics/AICoreWeaveCapitalSpreadSign20261012Exact.agda",
        ["coreWeaveCapitalSpreadSignNegative", "numericROICStillOpen", "numericWACCStillOpen"],
    )
    require(
        "DASHI/Economics/AICoreWeaveCapitalReinvestmentCoverage20261012Exact.agda",
        ["coreWeaveCashFundingShortfallIs10454", "coreWeaveReplacementCapexStillUnidentified"],
    )
    require(
        "DASHI/Economics/AICoreWeaveCapexDecompositionNonidentifiability20261012Exact.agda",
        ["aggregateCapexDoesNotDetermineReplacement", "replacementCoordinateSeparatesCollision"],
    )
    require(
        "DASHI/Economics/AICoreWeaveAssetLifeObsolescenceBoundary20261012Exact.agda",
        ["technologyEquipmentUsefulLifeMonthsIs72", "replacementScheduleStillOpen"],
    )
    require(
        "DASHI/Economics/AICoreWeaveMicrosoftTerminalPayerBoundary20261012Exact.agda",
        ["selectedNamedPayerCapacityIsPaid", "completeTerminalPayerProvenanceStillOpen"],
    )
    require(
        "DASHI/Economics/AICoreWeaveNamedPayerSaturation20261012Exact.agda",
        ["metaExternalCashEdgePaid", "openAIContractEdgePaidCashProvenanceOpen", "anonymousCurrentTopCustomerIdentityStillOpen"],
    )
    require(
        "DASHI/Economics/AITerminalPayerConsumerSufficiency20261012Exact.agda",
        ["selectedMicrosoftCapacityConsumerPaid", "selectedMetaCapacityConsumerPaid", "selectedOpenAICashConsumerOpen", "coreWeaveExhaustiveIndependenceConsumerOpen"],
    )
    require(
        "DASHI/Economics/AICapitalObserverNonDescent20261012Exact.agda",
        ["headlineSurfaceCannotDetermineCapitalRecovery", "everyTerminalPayerRepairMustSeparateWitness"],
    )
    require(
        "DASHI/Economics/AIPolicyCausalAdmission20261012Exact.agda",
        ["sameBasisBurdenMeasurementStillOpen", "reviewedCausalBridgeStillOpen"],
    )
    require(
        "DASHI/Economics/AISameCapabilityScarcityRentAdmission20261012Exact.agda",
        ["selectedPairCapabilityMatchedIsFalse", "matchedScarcityRentAdmissionStillOpen"],
    )
    require(
        "DASHI/Economics/AISameModelSelfHostCostBoundary20261012Exact.agda",
        ["sameModelIdentityPaid", "engineeringCostDoesNotCreateProviderMargin"],
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
            "AICoreWeaveCapitalSpreadSign20261012Exact",
            "AICoreWeaveCapitalReinvestmentCoverage20261012Exact",
            "AICoreWeaveCapexDecompositionNonidentifiability20261012Exact",
            "AICoreWeaveAssetLifeObsolescenceBoundary20261012Exact",
            "AICoreWeaveMicrosoftTerminalPayerBoundary20261012Exact",
            "AICoreWeaveNamedPayerSaturation20261012Exact",
            "AITerminalPayerConsumerSufficiency20261012Exact",
            "AICapitalObserverNonDescent20261012Exact",
            "AIPolicyCausalAdmission20261012Exact",
            "AISameCapabilityScarcityRentAdmission20261012Exact",
            "AISameModelSelfHostCostBoundary20261012Exact",
            "AIMaxCutReconciliation20261012FinalExact",
        ],
    )
