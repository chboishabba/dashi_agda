from pathlib import Path

MODULE = Path(
    "DASHI/Physics/ExoticGravity/AntigravityP1MarkedOSParetoReuseMaxCutExact.agda"
)


def test_p1_reuses_master_marked_os_pareto_frontier():
    text = MODULE.read_text()
    for needle in (
        "CMP119CosmologyMarkedStressOSParetoFrontierExact",
        "CMP119CosmologyMarkedStressSelectedSemanticsExact",
        "CMP119CosmologyMarkedStressE1DifferentiatedCovarianceExact",
        "CMP119CosmologyMarkedStressE2CylinderEmbeddingExact",
        "CMP119CosmologyMarkedStressE4ClusteringExact",
        "remainingOpaqueAnalyticEstimateCount = 0",
        "remainingAntigravitySpecificP1ResidualCount = 3",
        "e1DerivativeEquivarianceStillRequired = true",
        "e2StressCylinderEmbeddingStillRequired = true",
        "e4StressSourceSelectionAndOS4SemanticsStillRequired = true",
    ):
        assert needle in text


def test_terminal_laws_are_not_recharged_independently_after_marked_os_root():
    text = MODULE.read_text()
    for needle in (
        "independentRestT01LawRequired = false",
        "independentBoostInvarianceLawRequired = false",
        "independentRankTwoTransformLawRequired = false",
        "independentIsotropicTraceLawRequired = false",
        "independentR136TraceContinuationLawRequired = false",
        "b0TopologyBridgeChargedAsAntigravitySpecificLeaf = false",
        "b3LocalityBridgeChargedAsAntigravitySpecificLeaf = false",
    ):
        assert needle in text
