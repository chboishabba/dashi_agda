from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_post_scalar_vacuum_frontier_stops_at_metric_response_not_representation():
    text = read(
        "DASHI/Physics/Foundations/"
        "CMP119AntigravityPostScalarVacuumMaxCutExact.agda"
    )
    for token in (
        "preferredScalarVacuumRepresentationPaid",
        "betaAndNormalizationCoordinatesComplementary",
        "vacuumValueRecoveryAssumedPaid",
        "metricFamilyDifferentiabilityStillRequired",
        "renormalizedMetricResponseSameStateStillRequired",
        "cosmologicalRenormalizationConditionStillRequired",
        "sameStateEuclideanLorentzianContinuationStillRequired",
        "moreVacuumProjectorPlumbingCountsAsProgress",
    ):
        assert token in text
