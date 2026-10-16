from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULE = ROOT / "DASHI/Physics/ExoticGravity/AntigravitySameStateFourChannelDiscriminatorExact.agda"


def text() -> str:
    assert MODULE.is_file(), f"missing {MODULE}"
    return MODULE.read_text(encoding="utf-8", errors="replace")


def test_same_metric_state_feeds_all_four_observables():
    s = text()
    for needle in (
        "SameStateFourChannelPrediction",
        "weightFromSameMetric",
        "freeFallFromSameMetric",
        "clockFromSameMetric",
        "opticalFromSameMetric",
        "sameMetricFeedsAllFourChannels",
        "weightOnlyCannotPromoteMetricClaim",
    ):
        assert needle in s


def test_exact_nambu_kottler_fixture_is_reused_without_tt_promotion():
    s = text()
    for needle in (
        "fixtureOutwardFreeFall",
        "fixtureOutwardFreeFallIsFiveTwentyFourths",
        "fixtureExteriorLapseRoot",
        "fixtureInteriorLapseRoot",
        "fixtureMetricDelta",
        "fixtureMetricDeltaIsFourThirdsDeltaLambda",
        "scalarMetricPerturbationIsNotTTMode",
    ):
        assert needle in s


def test_mechanism_signatures_separate_metric_and_nonmetric_hypotheses():
    s = text()
    for needle in (
        "MechanismClass",
        "ordinaryForceConfounder",
        "inertiaOnlyCandidate",
        "scalarMetricCandidate",
        "propagatingTTCandidate",
        "MechanismSignature",
        "ordinaryForceHasNoIndependentMetricChannels",
        "scalarMetricHasClockAndOpticalMetricChannels",
        "ttRequiresAdditionalWaveSectorReceipt",
    ):
        assert needle in s


def test_experiment_receipt_binds_candidate_nuisance_and_cross_channel_consistency():
    s = text()
    for needle in (
        "CandidateBoundFourChannelExperiment",
        "sameCandidateAcrossAllChannels",
        "ordinaryMomentumClosed",
        "electromagneticBackgroundClosed",
        "thermalMechanicalBackgroundClosed",
        "crossChannelMetricConsistency",
        "replicationRequired",
        "anomalyAloneIsNotGeometry",
    ):
        assert needle in s
