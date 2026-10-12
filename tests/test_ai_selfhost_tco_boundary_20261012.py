from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_rented_gpu_comparator_is_not_owned_hardware_tco() -> None:
    require(
        "DASHI/Economics/AISameModelSelfHostCostBoundary20261012Exact.agda",
        [
            "gpuRentalTariffBasisPaid",
            "ownedHardwareTCOPaidIsFalse",
            "separateDepreciationModelPaidIsFalse",
            "separateEnergyModelPaidIsFalse",
            "separateFinancingCostPaidIsFalse",
            "engineerTimePaidIsFalse",
            "rentalTariffDoesNotCreateOwnedHardwareTCO",
        ],
    )
