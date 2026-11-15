from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_r136_vacuum_readout_compiles_to_static_receipt():
    text = read("DASHI/Physics/Foundations/CMP119AntigravityR136ToStaticVacuumPromotionExact.agda")
    for token in (
        "R136StaticVacuumPromotionInput",
        "compileR136VacuumToStaticReceipt",
        "compiledStaticAmplitudeUsesAffineCalibration",
        "r136CanProduceStaticReceiptAfterAffineCalibration",
        "independentStaticMetricResponseReceiptRequiredAfterR136Promotion",
        "affineNormalizationToGravityCalibrationStillRequired",
    ):
        assert token in text


def test_common_r136_pair_compiles_to_differential_receipt():
    text = read("DASHI/Physics/Foundations/CMP119AntigravityR136StaticPairToDifferentialExact.agda")
    for token in (
        "CommonR136AffineVacuumPair",
        "asCommonStaticPair",
        "r136StaticPairToDifferentialMetricResponse",
        "r136PairDeltaLambdaIsCalibratedSourceDifference",
        "r136CanProduceStaticAndDifferentialConsumersWithOneSharedCalibration",
        "independentDeltaSameObjectTheoremRequiredAfterCommonR136Pair",
    ):
        assert token in text
