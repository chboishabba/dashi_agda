from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_source_native_shortest_path_separates_alternative_routes():
    text = read("DASHI/Physics/ExoticGravity/AntigravitySourceNativeShortestPathMaxCutExact.agda")
    for token in (
        "VacuumIsraelRouteBoundary",
        "ContinuumStressRouteBoundary",
        "thinWallVacuumRouteRequiresR136ResponseWeld",
        "continuumStressRouteRequiresSourceVacuumIsraelAdmission",
        "sourceToGeometryAdmissionAndR136AreAlternativePayments",
        "finiteThicknessWallRequiredForThinWallClosure",
        "sourceNativePotentialDynamicsRequiredForThinWallClosure",
    ):
        assert token in text


def test_thin_wall_route_does_not_double_charge_continuum_stress_weld():
    text = read("DASHI/Physics/ExoticGravity/AntigravitySourceNativeShortestPathMaxCutExact.agda")
    assert "thinWallVacuumRouteRequiresR136ResponseWeld = false" in text
    assert "finiteThicknessWallRequiredForThinWallClosure = false" in text
    assert "sourceNativePotentialDynamicsRequiredForThinWallClosure = false" in text


def test_continuum_stress_route_does_not_double_charge_israel_admission():
    text = read("DASHI/Physics/ExoticGravity/AntigravitySourceNativeShortestPathMaxCutExact.agda")
    assert "continuumStressRouteRequiresSourceVacuumIsraelAdmission = false" in text
    assert "sourceToGeometryAdmissionAndR136AreAlternativePayments = true" in text


def test_terminal_exports_shortest_path_owner():
    text = read("DASHI/Physics/ExoticGravity/Everything.agda")
    assert "AntigravitySourceNativeShortestPathMaxCutExact" in text
