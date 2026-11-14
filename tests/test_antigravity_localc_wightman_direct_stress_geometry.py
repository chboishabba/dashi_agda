from pathlib import Path

MODULE = Path(
    "DASHI/Physics/Foundations/CMP119AntigravityLocalCWightmanDirectStressGeometryExact.agda"
)


def test_direct_wightman_stress_feeds_normalized_geometry_without_source_affine_map():
    text = MODULE.read_text()
    for needle in (
        "localCWightmanVacuumRho",
        "positiveLocalCWightmanRhoHasNormalizedStaticGeometry",
        "GRQFTSingleVacuumPositiveSourceNormalizedGeometryExact",
        "affineSourceNormalizationCalibrationRequiredForDirectStressRoute = false",
    ):
        assert needle in text


def test_direct_stress_route_keeps_real_physical_boundaries_open():
    text = MODULE.read_text()
    for needle in (
        "positiveTerminalRhoStillRequired = true",
        "cosmologicalRenormalizationConventionStillPhysical = true",
        "physicalStressLengthSquaredScaleStillExternal = true",
    ):
        assert needle in text
