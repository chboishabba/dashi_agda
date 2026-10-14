from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_owned_selfhost_tco_envelope_surface() -> None:
    require(
        "DASHI/Economics/AIOwnedSelfHostTCOEnvelope20261012Exact.agda",
        [
            "mi355xReferenceSystemWattsPerGPUIs1750",
            "usIndustrialElectricityJune2026Is917HundredthCentPerKWh",
            "rentalTariffCentsPerGPUHourIs259",
            "rentalNodeIncludesHostResources",
            "rentalNodeGPUCountIs8",
            "rentalNodeVCPUCountIs252",
            "rentalNodeRAMGiBIs2872",
            "benchmarkElectricityCostAbout1605HundredthCentPerGPUHour",
            "annualRentalBudgetPerGPUIs2268840Cents",
            "annualNonElectricHeadroomAbout2128264Cents",
            "purchasePriceStillOpen",
            "ownedTCOStillOpen",
        ],
    )
