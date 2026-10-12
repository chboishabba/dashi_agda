from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_nonidentifiability_compiles_to_discriminating_language_extension():
    text = read(
        "DASHI/Physics/Foundations/"
        "CMP119AntigravityVacuumExperimentDiscriminatorExact.agda"
    )
    for token in (
        "CurrentSourceViewAtScale",
        "currentSourceViewAtScale",
        "canonicalVacuumObserverCollision",
        "vacuumReadoutBundleAtScale",
        "vacuumReadoutSeparatesCanonicalCollision",
        "canonicalVacuumDiscriminatingExtension",
        "currentSourceViewCannotCloseVacuumConsumer",
        "physicalVacuumMeasurementStillRequiresCalibration",
    ):
        assert token in text


def test_terminal_scheduler_imports_vacuum_discriminator_owner():
    text = read(
        "DASHI/Physics/ExoticGravity/AntigravityPostNormalizationMaxCutExact.agda"
    )
    assert "CMP119AntigravityVacuumExperimentDiscriminatorExact" in text
    assert "vacuumDiscriminatorLanguageExtensionOwned" in text
