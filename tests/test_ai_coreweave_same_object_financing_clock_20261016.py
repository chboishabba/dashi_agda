from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_same_object_financing_clock_correction_owner_exists_and_pins_boundary():
    path = ROOT / "DASHI/Economics/AICoreWeaveSameObjectFinancingClock20261016Exact.agda"
    text = path.read_text(encoding="utf-8")
    for marker in [
        "sameObjectSixYearDepreciationPaid",
        "sameObjectFiveAndHalfToSixAndHalfYearRangePaid",
        "generic36To48MonthHorizonIsNotSameObject",
        "old24To36MonthMismatchNotPromotable",
        "usedGPUContributionRetainsSixYearBasis",
    ]:
        assert marker in text
