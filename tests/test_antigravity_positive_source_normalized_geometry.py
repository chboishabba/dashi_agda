from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_positive_source_can_be_normalized_to_existing_safe_fixture():
    text = read(
        "DASHI/Physics/Foundations/"
        "GRQFTSingleVacuumPositiveSourceNormalizedGeometryExact.agda"
    )
    for token in (
        "canonicalSafePhysicalAmplitude",
        "positiveSourceCalibrationFactor",
        "positiveSourceCalibrationFactorPositive",
        "calibratedAmplitude",
        "calibratedAmplitudeIsCanonicalSafeAmplitude",
        "canonicalSafeMassPositive",
        "canonicalSafeOutwardAccelerationPositive",
        "canonicalSafeNECDECMarginPositive",
        "canonicalSafeSECViolationMarginPositive",
        "positiveSourceHasNormalizedStaticGeometry",
        "physicalCalibrationValueStillExternal",
    ):
        assert token in text


def test_promotion_frontier_uses_general_positive_normalization_compiler():
    text = read(
        "DASHI/Physics/ExoticGravity/"
        "AntigravitySingleVacuumPhysicalPromotionMaxCutExact.agda"
    )
    assert "GRQFTSingleVacuumPositiveSourceNormalizedGeometryExact" in text
    assert "positiveSourceNormalizedGeometryCompilerOwned" in text
