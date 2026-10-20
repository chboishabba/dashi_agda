from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_coreweave_osint_capacity_vintage_surface() -> None:
    require(
        "DASHI/Economics/AICoreWeaveOSINTCapacityVintage20261014Exact.agda",
        [
            "coreWeaveJune2026CapacityVintage",
            "capacityAddedSince2025ShareBpIs7600",
            "capacityAddedSince2024ShareBpIs9533",
            "medianCapacityVintageAgeLowerMonthsIs6",
            "medianCapacityVintageAgeUpperMonthsIs12",
            "weightedMeanAgeLowerHundredthsIs748",
            "weightedMeanAgeUpperHundredthsIs1470",
            "capacityVintageDoesNotIdentifyHardwareAge",
            "netCapacityGrowthDoesNotIdentifyNoRetirements",
        ],
    )
