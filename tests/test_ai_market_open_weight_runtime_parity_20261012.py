from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_runtime_parity_surface() -> None:
    require(
        "DASHI/Economics/AIMarketOpenWeightRuntimeParity20261012Exact.agda",
        [
            "vercelOpenWeightSnapshot20261010",
            "openWeightPlatformShareBpIs6130",
            "globalOpenWeightShareStillOpen",
            "marketStressEventSeries20261012",
            "broadDirectionFlipObserved",
            "aiFinancingWindowStressObserved",
            "fixedAIBasketVolatilityStillOpen",
            "fixedAIBasketFlipRateStillOpen",
        ],
    )


def test_rollup_imports_runtime_parity() -> None:
    require(
        "DASHI/Economics/AIEntanglementEverything2026.agda",
        ["AIMarketOpenWeightRuntimeParity20261012Exact"],
    )
