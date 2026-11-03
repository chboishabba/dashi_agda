from pathlib import Path

MODULE = Path(
    "DASHI/Physics/ExoticGravity/AntigravityP1A2CertifiedStressCylinderExact.agda"
)


def test_a2_certificate_requires_pair_evaluator_to_equal_canonical_localc_observable():
    text = MODULE.read_text()
    for needle in (
        "ordinaryObservableOfPair",
        "selectedPairImageIsCanonicalLocalCStressObservable",
        "compileCertifiedFunctionalPresentation",
        "CMP119CosmologyA2LocalCWilsonPresentationCompilerExact",
        "CMP119CosmologyR109FunctionalStressCylinderPresentationExact",
    ):
        assert needle in text


def test_a2_certificate_does_not_recharge_wilson_admissibility():
    text = MODULE.read_text()
    for needle in (
        "observableChoiceCompilerOwned = true",
        "positiveTimeCompilerOwnedAfterSameObjectWeld = true",
        "gaugeInvarianceCompilerOwnedAfterSameObjectWeld = true",
        "pairEvaluatorSameObjectSemanticsStillRequired = true",
    ):
        assert needle in text
