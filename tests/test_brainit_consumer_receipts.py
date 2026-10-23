"""Static source-surface guard, not Agda kernel or fMRI evaluation."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def _read(relative):
    return (ROOT / relative).read_text(encoding="utf-8")


def test_primary_source_15_minute_not_secondary_only():
    source = _read("DASHI/Biology/BrainITSourceBoundaryExact.agda")
    assert "fifteenMinuteSubjectOneTransferIsPrimaryPaperClaim" in source
    assert "fifteenMinuteSubjectOneSampleCount" in source
    assert "450 refl" in source
    assert "fifteenMinuteRecognisableImageIsPrimaryPaperClaimIsFalse" not in source
    assert "arbitraryThoughtReadingSupportedIsFalse" in source


def test_consumer_collision_uses_generic_proof_not_boolean_only():
    proof = _read("DASHI/Biology/BrainITConsumerRelativeExact.agda")
    assert "Coarse.collisionRefutesEveryCoarsePrediction" in proof
    assert "Neural.fmriProjectionCollision" in proof
    assert "factorisationRequiresFibreAgreement" in proof
    assert "noUniversalLaplacianDecoder" in proof
    assert "coarseObservationConsumerRetained" in proof


def test_transcription_t7_t2_t3_without_replay_promotion():
    metrics = _read("DASHI/Biology/BrainITTableReceiptsExact.agda")
    for marker in [
        "subjectOne15min = metricRow 336 476 913",
        "subjectOne30min = metricRow 378 480 933",
        "subjectOne60min = metricRow 396 484 947",
        "clusteringRow functional = metricRow 386 486 964",
        "clusteringRow threeDCoordinates = metricRow 378 491 956",
        "reportedClusterPixelCorrMilli fiveTwelve = 392",
        "true false false false false false",
        "metricsIndependentlyRecomputed",
    ]:
        assert marker in metrics
    assert "clusterCountPixelCorrMilli _ = 0" not in metrics


def test_integrated_regression_and_roadmap():
    spine = _read("DASHI/Biology/BrainITValidation.agda")
    umbrella = _read("DASHI/Biology/Everything.agda")
    for owner in ["BrainITConsumerRelativeExact", "BrainITTableReceiptsExact",
                  "BrainITConnectomeFMRIWeldExact"]:
        assert owner in spine
        assert owner in umbrella
    roadmap = _read("Docs/BrainITDASHIBrainCMSRoadmap.md")
    assert "P0" in roadmap and "P1" in roadmap and "P2" in roadmap
    assert "Fly optical calcium != human BOLD fMRI" in roadmap
