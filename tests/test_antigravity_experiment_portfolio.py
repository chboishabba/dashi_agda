from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULE = ROOT / "DASHI/Physics/ExoticGravity/AntigravityExperimentPortfolioExact.agda"


def text() -> str:
    assert MODULE.is_file(), f"missing {MODULE}"
    return MODULE.read_text(encoding="utf-8", errors="replace")


def test_portfolio_has_non_scalar_discrimination_targets():
    s = text()
    for needle in (
        "AntigravityExperimentCandidate",
        "weightOnlyExperiment",
        "freeFallClockExperiment",
        "matchedFourChannelExperiment",
        "matchedFourChannelTTExperiment",
        "DiscriminationCoverage",
        "metricVsNonmetric",
        "crossChannelMetricConsistency",
        "scalarVsPropagatingTT",
        "ordinaryNuisanceClosure",
    ):
        assert needle in s


def test_matched_four_channel_strictly_adds_discrimination_without_claiming_truth():
    s = text()
    for needle in (
        "matchedFourChannelCoversMetricDiscrimination",
        "matchedFourChannelCoversCrossChannelConsistency",
        "weightOnlyDoesNotCoverMetricDiscrimination",
        "weightOnlyDoesNotCoverCrossChannelConsistency",
        "experimentCoverageCreatesTruth = false",
        "experimentCoverageCreatesMechanismIdentity = false",
    ):
        assert needle in s


def test_tt_option_is_optional_and_requires_p4():
    s = text()
    for needle in (
        "ttOptionRequiresP4",
        "fourChannelScalarRouteRequiresP4 = false",
        "matchedFourChannelTTSeparatesScalarFromTT",
        "scalarMetricDoesNotSupplyTTReceipt",
    ):
        assert needle in s


def test_portfolio_reuses_core_experiment_design_without_importing_sibling_authority():
    s = text()
    for needle in (
        "RobustExperimentInferenceFrontierExact as Robust",
        "antigravityExperimentDesign",
        "siblingPR1163ImportedAsTheoremAuthority = false",
        "siblingPR1165ImportedAsTheoremAuthority = false",
    ):
        assert needle in s
