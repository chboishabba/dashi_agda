from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_named_facility_delivery_surface():
    text = (ROOT / "DASHI/Economics/AICoreWeaveNamedFacilityDelivery20261014Exact.agda").read_text(encoding="utf-8")
    for marker in [
        "coreScientificCoreWeaveDelivery",
        "namedBillingFloorMWIs430",
        "daltonPhaseOneMWIs30",
        "fullContractedHostMWIs590",
        "namedHostCapacityDoesNotAutoAddToCoreWeaveActivePower",
    ]:
        assert marker in text
