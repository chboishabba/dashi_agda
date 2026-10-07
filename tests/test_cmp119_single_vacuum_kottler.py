from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    p = ROOT / rel
    assert p.is_file(), f"missing {rel}"
    return p.read_text(encoding="utf-8", errors="replace")


def test_single_vacuum_fixture_has_positive_mass_repulsion_and_dec():
    text = read("DASHI/Physics/Foundations/GRQFTSingleVacuumIsraelKottlerExact.agda")
    for token in (
        "sameVacuumAmplitude",
        "sameVacuumMass",
        "fixtureLambdaIsFiveTwelfths",
        "fixtureMassIsNineteenTwoTwentyFifths",
        "fixtureOutwardScaledIsSeventySevenSeventyFifths",
        "fixtureNECDECMarginIsEightTwoTwentyFifths",
        "fixtureSECViolationMarginIsFourTwoTwentyFifths",
        "twoDifferentVacuumAmplitudesRequired",
    ):
        assert token in text


def test_terminal_prefers_single_source_vacuum_static_route():
    text = read("DASHI/Physics/ExoticGravity/AntigravityABCDETerminalMaxCutExact.agda")
    assert "singleSourceVacuumStaticRouteConstructed" in text
    assert "twoDistinctSourceVacuumScalesRequired" in text
    assert "singleSourceAmplitudeAdmissibilityStillOpen" in text
