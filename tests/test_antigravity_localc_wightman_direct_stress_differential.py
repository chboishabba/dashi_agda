from pathlib import Path

MODULE = Path(
    "DASHI/Physics/Foundations/CMP119AntigravityLocalCWightmanDirectStressDifferentialExact.agda"
)


def test_direct_stress_pair_uses_delta_rho_without_source_affine_map():
    text = MODULE.read_text()
    for needle in (
        "directStressDeltaLambda",
        "directStressMetricTTDelta",
        "sharedAffineSourceNormalizationCalibrationRequired = false",
        "commonCosmologicalRenormalizationStillRequired = true",
    ):
        assert needle in text


def test_direct_stress_pair_keeps_tt_and_si_boundaries():
    text = MODULE.read_text()
    for needle in (
        "physicalStressLengthSquaredScaleStillExternal = true",
        "scalarMetricDifferenceAlreadyTTMode = false",
        "CommonCosmologicalRenormalization",
    ):
        assert needle in text
