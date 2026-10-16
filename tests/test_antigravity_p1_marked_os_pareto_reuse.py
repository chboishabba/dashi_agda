from pathlib import Path

MODULE = Path(
    "DASHI/Physics/ExoticGravity/AntigravityP1MarkedOSParetoReuseMaxCutExact.agda"
)


def test_p1_reuses_master_marked_os_pareto_frontier():
    text = MODULE.read_text()
    for needle in (
        "CMP119CosmologyMarkedStressOSParetoFrontierExact",
        "CMP119CosmologyMarkedStressSelectedSemanticsExact",
        "CMP119CosmologyPreferredSourcePhysicsMaxCut20261004QExact",
        "AntigravityP1SemanticSourceFrontierExact",
        "remainingOpaqueAnalyticEstimateCount = 0",
        "remainingAntigravitySpecificP1ResidualCount = 2",
        "q1PathDerivativeSemanticsAndEquivarianceStillRequired = true",
        "primitiveE1DerivativeEquivarianceProjectRequired = false",
        "e24SelectedObservableChoiceStillRequired = false",
        "e24PositiveTimeAdmissibilityStillRequired = false",
        "e24GaugeInvariantAdmissibilityStillRequired = false",
        "e24PairToCanonicalObservableSemanticsStillRequired = true",
        "e24ArbitraryMeaningPredicateRequired = false",
        "allStressCylinderEncodingRequired = false",
        "independentE4StressSelectionRequired = false",
        "independentE4DecayEstimateRequired = false",
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
