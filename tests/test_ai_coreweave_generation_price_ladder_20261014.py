from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_generation_price_ladder_surface():
    text = (ROOT / "DASHI/Economics/AICoreWeaveGenerationPriceLadder20261014Exact.agda").read_text(encoding="utf-8")
    for marker in [
        "coreWeaveCurrentGenerationPriceLadder",
        "a100PerGPUHourMillsIs2700",
        "h100PerGPUHourMillsIs6155",
        "h200PerGPUHourMillsIs6305",
        "b200PerGPUHourMillsIs8600",
        "gb200PerGPUHourMillsIs10500",
        "priceCrossSectionDoesNotIdentifyDepreciationCurve",
    ]:
        assert marker in text
