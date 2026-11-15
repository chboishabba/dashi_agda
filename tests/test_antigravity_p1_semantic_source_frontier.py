from pathlib import Path

MODULE = Path(
    "DASHI/Physics/ExoticGravity/AntigravityP1SemanticSourceFrontierExact.agda"
)


def test_p1_frontier_retires_compiler_owned_e24_presentation_debt():
    text = MODULE.read_text()
    for needle in (
        "CMP119CosmologyA2LocalCWilsonPresentationCompilerExact",
        "CMP119CosmologyR109PairObservableUnderdeterminationExact",
        "AntigravityP1A2CertifiedStressCylinderExact",
        "selectedObservableChoiceStillRequired = false",
        "positiveTimeAdmissibilityStillRequired = false",
        "gaugeInvariantAdmissibilityStillRequired = false",
        "pairToCanonicalLocalCObservableSemanticsStillRequired = true",
        "a2SameObjectReceiptCompilesCertifiedWilsonPresentation = true",
    ):
        assert needle in text


def test_p1_frontier_has_exactly_q1_and_a2_source_leaves():
    text = MODULE.read_text()
    for needle in (
        "q1PathDerivativeSourcePackageStillRequired = true",
        "remainingP1SourceLeafCount = 2",
        "remainingOpaqueAnalyticEstimateCount = 0",
        "remainingP1WorkIsSourceSemantics = true",
    ):
        assert needle in text
