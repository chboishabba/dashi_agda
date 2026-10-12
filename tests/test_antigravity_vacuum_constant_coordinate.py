from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_vacuum_nonidentifiability_uses_constant_remainder_coordinate_not_plaquette():
    text = read(
        "DASHI/Physics/Foundations/"
        "CMP119AntigravityVacuumSequenceNonidentifiabilityExact.agda"
    )
    assert "vacuumConstantProjection" in text
    assert "irrelevantCoefficientField" in text
    assert "unitVacuumSequence _ = T4.irrelevantAction 1ℚ" in text
    assert "projectedVacuum = vacuumConstantProjection" in text


def test_localized_vacuum_readout_uses_constant_coordinate_and_keeps_source_semantics_open():
    text = read(
        "DASHI/Physics/Foundations/"
        "CMP119AntigravityLocalizedVacuumReadoutExact.agda"
    )
    for token in (
        "localizedVacuumConstantReadout",
        "T4.irrelevantCoefficientField",
        "VacuumConstantEncodingReceipt",
        "vacuumSectorIsConstantAction",
        "plaquetteProjectorIsNotVacuumConstantReadout",
        "publishedVacuumConstantEncodingStillRequired",
    ):
        assert token in text
