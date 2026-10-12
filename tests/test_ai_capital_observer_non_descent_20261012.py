from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_ai_capital_observer_non_descent_surface() -> None:
    require(
        "DASHI/Economics/AICapitalObserverNonDescent20261012Exact.agda",
        [
            "headlineSurfaceCannotDetermineCapitalRecovery",
            "terminalPayerCollision",
            "capitalSpreadCollision",
            "everyTerminalPayerRepairMustSeparateWitness",
            "everyCapitalSpreadRepairMustSeparateWitness",
            "headlineMetricsDoNotAutoFactorCapitalRecovery",
        ],
    )


def test_ai_capital_rollup_imports_non_descent_owner() -> None:
    require(
        "DASHI/Economics/AIEntanglementEverything2026.agda",
        ["AICapitalObserverNonDescent20261012Exact"],
    )
