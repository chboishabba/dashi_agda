from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_coreweave_capex_decomposition_nonidentifiability_surface() -> None:
    require(
        "DASHI/Economics/AICoreWeaveCapexDecompositionNonidentifiability20261012Exact.agda",
        [
            "aggregateCapexCollisionPaid",
            "replacementCoordinateSeparatesCollision",
            "aggregateCapexDoesNotDetermineReplacement",
            "maintenanceReplacementStillRequiresExternalCoordinate",
        ],
    )


def test_rollup_imports_capex_decomposition_owner() -> None:
    require(
        "DASHI/Economics/AIEntanglementEverything2026.agda",
        ["AICoreWeaveCapexDecompositionNonidentifiability20261012Exact"],
    )
