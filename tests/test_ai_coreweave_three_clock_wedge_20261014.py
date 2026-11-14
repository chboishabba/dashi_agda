from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_coreweave_three_clock_wedge():
    text = (ROOT / "DASHI/Economics/AICoreWeaveThreeClockCapitalRecovery20261014Exact.agda").read_text(encoding="utf-8")
    for marker in [
        "coreWeaveThreeClockWedge",
        "lenderLowerMonthsIs36",
        "contractClockMonthsIs60",
        "bookClockMonthsIs72",
        "selectedClockOrderingPaid",
        "debtDueThrough2028ShareBpIs4223",
        "capacity36MonthWindowThrough2028ShareBpIs5666",
        "calendarOverlapDoesNotIdentifySameAssets",
    ]:
        assert marker in text
