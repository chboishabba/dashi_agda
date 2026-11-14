from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_delta_v_is_not_promoted_directly_to_delta_lambda():
    text = read("DASHI/Physics/Foundations/CMP119AntigravityDifferentialMetricResponseFirewallExact.agda")
    for token in (
        "normalizationDifferenceAloneDeterminesPhysicalDeltaLambda",
        "DifferentialMetricResponseReceipt",
        "sameStateMetricResponseDifferenceRequired",
        "commonCosmologicalRenormalizationConditionRequired",
        "normalizationCountertermCancellationStillUseful",
        "physicalDeltaLambda",
    ):
        assert token in text


def test_scalar_metric_compiler_distinguishes_candidate_and_physical_response():
    text = read("DASHI/Physics/ExoticGravity/AntigravitySingleVacuumDifferentialMetricCompilerExact.agda")
    for token in (
        "sourceModulationMetricTTDeltaIsCandidateUntilMetricResponseWeld",
        "physicalMetricTTDelta",
        "normalizationDifferenceAloneDeterminesPhysicalDeltaLambda",
        "sameStateMetricResponseDifferenceStillRequired",
    ):
        assert token in text
