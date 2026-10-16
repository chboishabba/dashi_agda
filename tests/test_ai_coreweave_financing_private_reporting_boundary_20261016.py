from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_financing_capstone_distinguishes_private_required_reporting_from_public_receipts():
    text = (ROOT / "DASHI/Economics/AICoreWeaveSameObjectFinancingMaxCut20261016Exact.agda").read_text(encoding="utf-8")
    for marker in [
        "namedOpenAIContractCashArchitecturePaid",
        "privateGPUIdentifierReportingRequired",
        "publicRealisedNamedCashStillOpen",
        "publicSerialInventoryStillOpen",
    ]:
        assert marker in text
