from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_positive_physical_lambda_compiles_to_dimensioned_radius_squared():
    text = read(
        "DASHI/Physics/Foundations/"
        "GRQFTSingleVacuumCalibratedRadiusSquaredExact.agda"
    )
    for token in (
        "canonicalFixtureQ",
        "canonicalFixtureQIsFiveThirds",
        "physicalLambdaQuantity",
        "radiusSquaredFromPhysicalLambda",
        "lambdaTimesRadiusSquaredIsCanonicalQ",
        "radiusSquaredFromPositiveLambdaIsPositive",
        "inverseAreaTimesAreaIsDimensionless",
        "squareRootNotRequiredForRadiusSquaredTarget",
        "absoluteSIDecimalScaleStillRequiresReceipt",
    ):
        assert token in text


def test_post_normalization_scheduler_imports_radius_squared_compiler():
    text = read(
        "DASHI/Physics/ExoticGravity/AntigravityPostNormalizationMaxCutExact.agda"
    )
    assert "GRQFTSingleVacuumCalibratedRadiusSquaredExact" in text
    assert "dimensionedRadiusSquaredCompilerOwned" in text
