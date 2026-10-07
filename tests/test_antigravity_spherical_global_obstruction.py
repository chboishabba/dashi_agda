from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    p = ROOT / rel
    assert p.is_file(), f"missing {rel}"
    return p.read_text(encoding="utf-8", errors="replace")


def test_spherical_positive_density_global_mass_obstruction_owner_exists():
    text = read("DASHI/Physics/Foundations/PositiveGSphericalExteriorMassObstructionExact.agda")
    for token in (
        "sphericalMassDerivative",
        "positiveDensityBuildsPositiveMass",
        "vacuumExteriorMassIsBoundaryMass",
        "positiveBoundaryMassGivesAttractiveSchwarzschildExterior",
        "positiveDensityAloneCannotYieldRepulsiveVacuumExterior",
    ):
        assert token in text


def test_outward_interior_requires_nonzero_boundary_stress_or_surface_layer():
    text = read("DASHI/Physics/Foundations/PositiveGSphericalInteriorRepulsionBoundaryExact.agda")
    for token in (
        "radialEinsteinNumerator",
        "outwardInteriorRequiresNegativeNumerator",
        "vacuumSmoothBoundaryWithPositiveMassHasPositiveNuPrime",
        "outwardInteriorCannotMeetSmoothZeroPressurePositiveMassBoundary",
        "surfaceLayerOrSignChangingProfileRequired",
    ):
        assert token in text


def test_terminal_maxcut_consumes_global_obstruction():
    text = read("DASHI/Physics/ExoticGravity/AntigravityABCDETerminalMaxCutExact.agda")
    for token in (
        "stageCSphericalExteriorMassObstruction",
        "stageCInteriorBoundaryObstruction",
        "repulsiveVacuumExteriorWithPositiveDensityStillOpen",
        "localInteriorMetricEngineeringRouteStillLive",
    ):
        assert token in text
