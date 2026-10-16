from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_phase2_knows_private_measurement_surfaces_exist_without_public_values():
    text = (ROOT / "DASHI/Economics/AICapitalPhase2Acquisition20261016Exact.agda").read_text(encoding="utf-8")
    for marker in [
        "sameInstrumentCreditRepricingPaid",
        "namedOpenAIContractMeasurementArchitecturePaid",
        "privateGPUIdentifierReportingRequired",
        "publicNamedOpenAICashPaidIsFalse",
        "publicSerialInventoryPaidIsFalse",
    ]:
        assert marker in text
