from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_localized_action_two_coordinates_are_jointly_complete():
    text = read(
        "DASHI/Physics/Foundations/"
        "CMP119LocalizedActionPlaquetteVacuumCoordinateBidiExact.agda"
    )
    for token in (
        "localizedActionCoordinates",
        "rebuildLocalizedAction",
        "localizedActionCoordinateRoundTrip",
        "plaquetteProjectionAloneNotInjective",
        "constantProjectionAloneNotInjective",
        "plaquetteAndConstantCoordinatesJointlyComplete",
        "betaAndNormalizationCoordinatesAreComplementary",
    ):
        assert token in text
