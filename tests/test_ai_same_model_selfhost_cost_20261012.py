from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_same_model_selfhost_cost_boundary() -> None:
    require(
        "DASHI/Economics/AISameModelSelfHostCostBoundary20261012Exact.agda",
        [
            "sameModelIdentityPaid",
            "selfHostCostCentsPerMillionIs93",
            "hostedCostCentsPerMillionIs120",
            "engineeringCostDoesNotCreateProviderMargin",
            "configurationSensitivityRetained",
        ],
    )


def test_rollup_imports_same_model_cost_boundary() -> None:
    require(
        "DASHI/Economics/AIEntanglementEverything2026.agda",
        ["AISameModelSelfHostCostBoundary20261012Exact"],
    )
