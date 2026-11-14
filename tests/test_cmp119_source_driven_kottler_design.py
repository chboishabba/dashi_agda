from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    p = ROOT / rel
    assert p.is_file(), f"missing {rel}"
    return p.read_text(encoding="utf-8", errors="replace")


def test_source_driven_design_inverts_exterior_amplitude():
    text = read("DASHI/Physics/Foundations/GRQFTSourceAmplitudeDrivenIsraelKottlerExact.agda")
    for token in (
        "massFromExteriorAmplitude",
        "exteriorAmplitudeInversion",
        "interiorAmplitudeEquation",
        "sourceAmplitudesNeedNotEqualFixtureFractions",
        "remainingSourceLeafIsAdmissibilityNotMagicValues",
    ):
        assert token in text


def test_terminal_replaces_magic_value_frontier_with_admissibility():
    text = read("DASHI/Physics/ExoticGravity/AntigravityABCDETerminalMaxCutExact.agda")
    assert "sourceNativeExactFixtureValuesRequired" in text
    assert "sourceAmplitudeAdmissibilityStillOpen" in text
