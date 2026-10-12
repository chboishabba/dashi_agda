from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_common_affine_static_pair_compiles_to_differential_receipt():
    text = read("DASHI/Physics/Foundations/CMP119AntigravityStaticPairToDifferentialMetricResponseExact.agda")
    for token in (
        "CommonRenormalizedVacuumPair",
        "staticPairToDifferentialMetricResponse",
        "normalizationDifferenceMatchesMetricResponseDifference",
        "independentDifferentialSameObjectTheoremRequiredAfterTwoStaticReceipts",
        "independentDifferentialSameObjectTheoremRequiredAfterCommonAffinePair",
        "commonAffineCalibrationRequired",
        "commonRenormalizationConventionRequired",
    ):
        assert token in text
