from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_coreweave_asset_life_boundary() -> None:
    require(
        "DASHI/Economics/AICoreWeaveAssetLifeObsolescenceBoundary20261012Exact.agda",
        [
            "technologyEquipmentUsefulLifeMonthsIs72",
            "maintenanceRepairsExpensedIsPaid",
            "accountingLifeDoesNotIdentifyEconomicObsolescence",
            "installedAgeDistributionStillOpen",
            "replacementScheduleStillOpen",
        ],
    )


def test_rollup_imports_asset_life_boundary() -> None:
    require(
        "DASHI/Economics/AIEntanglementEverything2026.agda",
        ["AICoreWeaveAssetLifeObsolescenceBoundary20261012Exact"],
    )
