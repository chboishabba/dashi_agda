from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_openai_ddtl3_weld_pays_named_contract_cash_architecture_not_realised_amounts():
    text = (ROOT / "DASHI/Economics/AICoreWeaveOpenAIDDTL3CashHardwareWeld20261016Exact.agda").read_text(encoding="utf-8")
    for marker in [
        "openAIPhoenix1NamedMSAPaid",
        "availableCashDefinitionIsActualCustomerCash",
        "msaPaymentRightsAreCollateralPaid",
        "contractRealisationRatioMechanismPaid",
        "gpuRackSerialReportingRequirementPaid",
        "publicRealisedOpenAICashAmountStillOpen",
        "publicGPUInventoryStillOpen",
    ]:
        assert marker in text
