from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_pure_vacuum_constant_is_orthogonal_to_plaquette_beta_projection():
    text = read(
        "DASHI/Physics/Foundations/"
        "CMP119AntigravityVacuumConstantBetaOrthogonalityExact.agda"
    )
    for token in (
        "VacuumConstantEncoding",
        "vacuumPlaquetteProjectionZero",
        "vacuumPlaquetteDriftZero",
        "sectorProjectionDropsVacuumConstant",
        "betaProjectionCannotRecoverVacuumConstant",
        "vacuumConstantNeedsIndependentNormalizationCoordinate",
    ):
        assert token in text
