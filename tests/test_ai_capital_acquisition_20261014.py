from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"

def test_financing_panel_owner():
    require("DASHI/Economics/AIFinancingConditionsPanel20261014Exact.agda", [
        "firmusWithdrawalObserved", "imfAISlowdownLeverageWarningObserved",
        "goldmanFinancingPressureObserved", "tencentDebtAccessObserved",
        "panelDoesNotCreateSectorBubble", "stressDoesNotCreateUniversalClosure"
    ])

def test_regulatory_cost_measurement_boundary():
    require("DASHI/Economics/AIAustraliaRegulatoryCostMeasurementBoundary20261014Exact.agda", [
        "businessImpactSurveyInstrumentObserved", "harmonisedRealisedCostVectorPaidIsFalse",
        "surveyInstrumentDoesNotCreateRealisedCostVector"
    ])

def test_contract_finance_matching_boundary():
    require("DASHI/Economics/AICoreWeaveAssetLevelContractFinance20261014Exact.agda", [
        "majorityCapexAssetLevelFinanced", "contractAmortisationStructureObserved",
        "investmentGradeCustomerLookthroughObserved", "financingStructureDoesNotCreateTerminalDemand"
    ])

def test_landlord_yield_boundary():
    require("DASHI/Economics/AIGalaxyHeliosLandlordEconomics20261014Exact.agda", [
        "startingGrossYieldBpIs1370", "leaseLevelMarginLowerBpIs9000",
        "phaseILeaseRevenueHundredThousandUSDIs189", "phaseIOperatorRevenueHundredThousandUSDIs58",
        "realisedLeaseRevenueObserved", "cashCollectionStillOpen",
        "landlordYieldDoesNotCreateCoreWeaveROIC", "contractedYieldDoesNotCreateRealisedCash"
    ])

def test_coreweave_downstream_concentration():
    require("DASHI/Economics/AICoreWeaveDownstreamLandlordConcentration20261014Exact.agda", [
        "coreWeaveRevenueShareBpIs7700", "contractedMWIs590", "billingMWIs395",
        "spvAssignmentObserved", "coreWeavePrimaryObligorObserved",
        "downstreamConcentrationDoesNotCreateCircularCash"
    ])

def test_oct14_roadmap_owner():
    require("DASHI/Economics/AICapitalRoadmapMaxCut20261014Exact.agda", [
        "capitalReturnMagnitudeBounded", "ownedNodeTCOPartial",
        "providerMarginalServingCostEmpirical", "terminalPayerGraphPartial",
        "replacementEconomicsEmpirical", "regulatoryBurdenEmpirical",
        "financingConditionsHeterogeneous", "landlordLayerReturnPaid",
        "additionalGenericAbstractionScheduledIsFalse"
    ])

def test_rollup_imports_oct14_acquisitions():
    require("DASHI/Economics/AIEntanglementEverything2026.agda", [
        "AIFinancingConditionsPanel20261014Exact",
        "AIAustraliaRegulatoryCostMeasurementBoundary20261014Exact",
        "AICoreWeaveAssetLevelContractFinance20261014Exact",
        "AIGalaxyHeliosLandlordEconomics20261014Exact",
        "AICoreWeaveDownstreamLandlordConcentration20261014Exact",
        "AICapitalRoadmapMaxCut20261014Exact"
    ])
