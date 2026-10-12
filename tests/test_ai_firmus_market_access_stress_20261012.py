from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_firmus_market_access_stress_surface() -> None:
    require(
        "DASHI/Economics/AIFirmusMarketAccessStress20261012Exact.agda",
        [
            "plannedIPOBillionUSDIs5",
            "impliedValuationTenthBillionUSDIs306",
            "ipoWithdrawnObserved",
            "investorSelectivityStressObserved",
            "sectorBubbleEstablishedIsFalse",
            "oneIssuerWithdrawalDoesNotCreateSectorBubble",
        ],
    )
