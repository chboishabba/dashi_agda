from pathlib import Path

MODULE = Path(
    "DASHI/Physics/ExoticGravity/AntigravityPostNormalizationDirectStressMaxCutExact.agda"
)


def test_preferred_typed_stress_route_does_not_require_source_affine_map():
    text = MODULE.read_text()
    for needle in (
        "preferredRouteConsumesTypedLocalCWightmanStressDirectly = true",
        "affineSourceNormalizationCalibrationRequiredForPreferredRoute = false",
        "directStaticNormalizedGeometryCompilerOwned = true",
        "directScalarDifferentialCompilerOwned = true",
    ):
        assert needle in text


def test_irreducible_p2_physics_is_common_renormalization_plus_scale():
    text = MODULE.read_text()
    for needle in (
        "acceptedMeasuredGStillRequired = false",
        "commonCosmologicalRenormalizationStillRequired = true",
        "stressLengthSquaredScaleStillRequired = true",
        "remainingPreferredP2PhysicalLeafCount = 2",
    ):
        assert needle in text
