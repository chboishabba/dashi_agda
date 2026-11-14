from pathlib import Path

MODULE = Path(
    "DASHI/Physics/ExoticGravity/AntigravityStressLengthSquaredTargetIntervalExact.agda"
)


def test_required_product_interval_is_compiler_owned_for_rational_kappa_points():
    text = MODULE.read_text()
    for needle in (
        "PhysicalEinsteinCouplingInterval",
        "RationalKappaPoint",
        "requiredStressLengthSquaredLower",
        "requiredStressLengthSquaredUpper",
        "requiredStressLengthSquaredAt",
        "requiredStressLengthSquaredEnclosed",
        "positiveDenominatorQuotientEnclosure",
        "remainingP2DatumIsSameApparatusStressLengthSquaredProduct = true",
        "rationalPointDiagnosticPromotesMeasuredKappaToExact = false",
    ):
        assert needle in text
