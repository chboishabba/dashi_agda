from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULE = ROOT / "DASHI/Physics/ExoticGravity/AntigravityP1A2OpenLemmaASTExact.agda"


def text() -> str:
    assert MODULE.is_file(), f"missing {MODULE}"
    return MODULE.read_text(encoding="utf-8", errors="replace")


def test_key_open_lemma_is_selected_pair_to_canonical_localc_stress():
    s = text()
    for needle in (
        "A2SelectedPairCanonicalLocalCStressLemma",
        "selectedRound109Pair",
        "canonicalLocalCStressObservable",
        "ordinaryObservableOfPair",
    ):
        assert needle in s


def test_typed_ast_separates_open_syntax_from_solution():
    s = text()
    for needle in (
        "A2Sort",
        "pairSort",
        "observableSort",
        "A2Term",
        "selectedPairTerm",
        "canonicalStressTerm",
        "evaluatePairTerm",
        "denoteA2Term",
        "A2OpenLemmaAST",
        "A2LemmaGoal",
        "A2LemmaSolution",
        "compileSolvedA2AST",
    ):
        assert needle in s


def test_unproven_invariants_are_bounded_by_least_privilege():
    s = text()
    for needle in (
        "a2SourceSemanticPackageCount = 1",
        "a2InternalOpenInvariantCount = 2",
        "evaluatorSourceSemanticsStillOpen = true",
        "selectedPairSameObjectEqualityStillOpen = true",
        "nonSelectedPairImagesConstrainedByA2 = false",
        "evaluatorInjectivityRequired = false",
        "evaluatorSurjectivityRequired = false",
        "allPairSemanticsRequired = false",
        "positiveTimeSeparatelyOpen = false",
        "gaugeInvarianceSeparatelyOpen = false",
        "clusteringSeparatelyOpen = false",
        "downstreamCovarianceSeparatelyOpen = false",
    ):
        assert needle in s


def test_ast_solution_compiles_existing_certified_a2_witness():
    s = text()
    assert "CertifiedA2.CertifiedA2PairObservableSemantics" in s
    assert "selectedPairImageIsCanonicalLocalCStressObservable" in s
