from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_coreweave_fleet_age_osint_capstone():
    text = (ROOT / "DASHI/Economics/AICoreWeaveFleetAgeOSINTMaxCut20261014Exact.agda").read_text(encoding="utf-8")
    for marker in [
        "capacityVintageIsNowPaid",
        "selectedCapacityMedianIs6To12Months",
        "capacityCannotRecoverHardwareAge",
        "multiGenerationCommercialCoexistenceIsPaid",
        "currentA100CommercialPriceCoordinatePaid",
        "selectedVintageWallShareIs5666Bp",
        "longitudinalPriceDecayStillOpen",
        "exactHardwareAgeStillOpen",
        "refreshHistoryStillOpen",
    ]:
        assert marker in text
