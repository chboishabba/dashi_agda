from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_coreweave_book_stock_youth_surface():
    text = (ROOT / "DASHI/Economics/AICoreWeaveBookStockYouth20261014Exact.agda").read_text(encoding="utf-8")
    for marker in [
        "coreWeaveBookStockYouth",
        "technologyEquipmentNetGrowthShareBpIs5624",
        "accumulatedDAShareBpIs1377",
        "h12026NetPPEGrowthBpIs5294",
        "bookStockYouthDoesNotIdentifyHardwareAge",
    ]:
        assert marker in text
