from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_same_object_financing_capstone_marks_paid_and_open_coordinates():
    text = (ROOT / "DASHI/Economics/AICoreWeaveSameObjectFinancingMaxCut20261016Exact.agda").read_text(encoding="utf-8")
    for marker in [
        "sameObjectDepreciationClockPaid",
        "projectSpecificFinancingSurfacePaid",
        "customerCreditFinancingCouplingPaid",
        "sameSPVFinanceToSiteMappingPaid",
        "sameInstrumentCreditRepricingPaid",
        "namedOpenAIContractCashArchitecturePaid",
        "privateGPUIdentifierReportingRequired",
        "contractRealisationEquityCureMechanismPaid",
        "covenantComplianceInsufficientForCustomerCashPaid",
        "exactFinancedGPUCohortStillOpen",
        "realisedProjectReturnStillOpen",
        "namedTerminalCashStillOpen",
    ]:
        assert marker in text
