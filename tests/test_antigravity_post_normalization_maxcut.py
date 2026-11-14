from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_normalization_receipt_closes_vacuum_algebra():
    text = read("DASHI/Physics/Foundations/CMP119AntigravityVacuumNormalizationToLorentzianStressExact.agda")
    for token in (
        "receiptLorentzianStress",
        "receiptVacuumLikeStress",
        "positiveRenormalizedAmplitudeGivesNegativeActiveStress",
        "positiveRenormalizedAmplitudeGivesNegativeTrace",
        "metricResponseReceiptIsTheOnlyStaticTensorPromotionLeaf",
    ):
        assert token in text


def test_post_normalization_frontier_retires_old_source_impasse():
    text = read("DASHI/Physics/ExoticGravity/AntigravityPostNormalizationMaxCutExact.agda")
    for token in (
        "vacuumNormalizationFlowAssumedPaid",
        "differentialVacuumDifferenceAssumedPaid",
        "oldBetaERBVacuumNonidentifiabilityStillTrueButNoLongerTerminal",
        "staticMetricResponseRenormalizationWeldStillRequired",
        "differentialScalarMetricResponseOwned",
        "differentialSpin2TTProducerStillRequired",
        "continuumR136RouteRemainsIndependentAlternative",
    ):
        assert token in text
