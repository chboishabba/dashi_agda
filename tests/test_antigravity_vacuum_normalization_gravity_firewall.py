from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_vacuum_normalization_is_not_automatically_gravitational_lambda():
    text = read("DASHI/Physics/Foundations/CMP119AntigravityVacuumNormalizationGravityFirewallExact.agda")
    for token in (
        "normalizationConstantAloneDeterminesGravitationalStress",
        "sourceVacuumReadoutAloneDeterminesPhysicalLambda",
        "renormalizedEffectiveActionMetricResponseRequired",
        "gravitationalCosmologicalRenormalizationConditionRequired",
        "differentialCommonCountertermCancellationStillValid",
        "VacuumNormalizationToGravityReceipt",
    ):
        assert token in text


def test_direct_source_vacuum_stress_is_demoted_to_candidate_shape():
    text = read("DASHI/Physics/Foundations/CMP119AntigravityDirectSourceVacuumStressExact.agda")
    for token in (
        "sourceVacuumStressAtScaleIsCandidateShape",
        "actualSourceVacuumCoefficientFeedsStressDirectly",
        "metricVolumeSameObjectReceiptRequiredForPhysicalPromotion",
        "cosmologicalRenormalizationReceiptRequiredForPhysicalPromotion",
    ):
        assert token in text
