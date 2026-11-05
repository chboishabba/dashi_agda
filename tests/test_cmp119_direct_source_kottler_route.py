from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    p = ROOT / rel
    assert p.is_file(), f"missing {rel}"
    return p.read_text(encoding="utf-8", errors="replace")


def test_direct_route_bypasses_pinned_r136_for_static_geometry():
    text = read("DASHI/Physics/Foundations/GRQFTCMP119DirectSourceKottlerRouteExact.agda")
    for token in (
        "sourceAmplitudePair",
        "sourceInteriorVacuumStress",
        "sourceExteriorVacuumStress",
        "sourceDrivenMass",
        "sourceExteriorStressUsesLiteralVacuumAmplitude",
        "pinnedR136NotRequiredForStaticGeometryConstruction",
    ):
        assert token in text


def test_terminal_marks_r136_as_crosscheck_not_static_blocker():
    text = read("DASHI/Physics/ExoticGravity/AntigravityABCDETerminalMaxCutExact.agda")
    assert "directSourceVacuumToKottlerRouteConstructed" in text
    assert "rawEq223ResponseToPinnedR136IsIndependentCrossCheck" in text
