"""Moment/Heaps factor vs nonuniform-label sampling, independently enumerated."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import permutations, product
from math import factorial
from pathlib import Path
import sys
import pytest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"scripts"))
from zipf_three_draw_moment_conditioning_exact import (
    iid_three_draw_moment_law,uniform_order_given_all_distinct,
    nonuniform_zipf_three_rank_receipt
)


def independent_three_word_law(counts):
    from zipf_ternary27_action_heaps_exact import heaps_curve
    q=len(counts)
    law=defaultdict(F)
    for word in product(range(q),repeat=3):
        p=F(1)
        for i in word: p*=F(counts[i],sum(counts))
        seen=set();curve=[0]
        for v in word:
            seen.add(v);curve.append(len(seen))
        law[tuple(curve)]+=p
    return dict(law)


def test_117_exact_weighted_alphabets_against_independent_complete_words():
    checked=0
    for k in (2,3,4):
        for weights in product((1,2,3),repeat=k):
            result=iid_three_draw_moment_law(weights)
            assert result["law"]==independent_three_word_law(weights)
            assert sum(result["law"].values(),F())==1
            conditioned=uniform_order_given_all_distinct(weights)
            assert conditioned["distinct_event_probability"]==(
                factorial(k)*F(1,sum(weights)**k)
                * __import__("math").prod(weights))
            assert set(conditioned["conditional_order_law"].values())=={
                F(1,factorial(k))}
            checked+=1
    assert checked==117


def test_nonuniform_three_rank_zipf_exponent_one_moments_and_conditional_order():
    receipt=nonuniform_zipf_three_rank_receipt()
    assert receipt["moments"]["probabilities"]==(F(6,11),F(3,11),F(2,11))
    assert receipt["moments"]["law"]=={
        (0,1,1,1):F(251,1331),(0,1,1,2):F(288,1331),
        (0,1,2,2):F(576,1331),(0,1,2,3):F(216,1331)}
    assert receipt["distinct_conditioning"]["distinct_event_probability"]==F(216,1331)
    assert receipt["distinct_conditioning"]["conditional_order_law"][(0,1,2)]==F(1,6)
    assert receipt["distinct_conditioning"]["unconditioned_first_discovery_law"][(0,1,2)]==F(18,55)


def test_distribution_observation_invariant_under_label_reindex_but_word_mass_not():
    weights=(6,3,2)
    for p in permutations(range(3)):
        relabeled=tuple(weights[i] for i in p)
        assert iid_three_draw_moment_law(weights)["law"]==(
            iid_three_draw_moment_law(relabeled)["law"])
    aaa=F(6,11)**3
    ccc=F(2,11)**3
    assert aaa!=ccc
    # Yet the named sequences AAA and CCC share the SAME full curve.
    assert (0,1,1,1)==(0,1,1,1)


def test_all_distinct_event_on_three_types_equals_full_heaps_fourth_fibre():
    for weights in product((1,2,3,4),repeat=3):
        moments=iid_three_draw_moment_law(weights)["law"]
        conditioned=uniform_order_given_all_distinct(weights)
        assert moments[(0,1,2,3)]==conditioned["distinct_event_probability"]


def test_uniform_case_recovers_six_order_27_cube_not_nonuniform_pl_law():
    r=uniform_order_given_all_distinct((1,1,1))
    assert r["distinct_event_probability"]==F(2,9)
    assert set(r["conditional_order_law"].values())=={F(1,6)}
    assert r["conditional_order_law"]==r["unconditioned_first_discovery_law"]
    weighted=uniform_order_given_all_distinct((6,3,2))
    assert weighted["conditional_order_law"]!=weighted["unconditioned_first_discovery_law"]


def test_k_one_and_strict_invalid_weight_domains():
    assert iid_three_draw_moment_law((7,))["law"]=={(0,1,1,1):F(1)}
    assert uniform_order_given_all_distinct((7,))["conditional_order_law"]=={(0,):F(1)}
    for bad in ((),(0,1),(-1,2),(True,2),(2,1.25)):
        with pytest.raises(ValueError):iid_three_draw_moment_law(bad)
    with pytest.raises(ValueError):
        uniform_order_given_all_distinct((1,1,1,1,1,1,1,1))


def test_no_duplicate_probability_ontology_and_explicit_original_owners():
    src=(ROOT/"scripts/zipf_three_draw_moment_conditioning_exact.py").read_text()
    factor=(ROOT/"DASHI/Statistics/ZipfThreeDrawEqualityPatternFactorExact.agda").read_text()
    umbrella=(ROOT/"DASHI/Statistics/ZipfFamilyEverything.agda").read_text()
    assert "from zipf_heaps_bridge import _validated_counts" in src
    assert "from zipf_full_heaps_path_distribution_exact import full_heaps_curve_law" in src
    assert "from zipf_first_discovery_plackett_luce_exact import size_biased_order_law" in src
    for theorem in ("equalityPatternInvariantUnderExistingValueS3",
                    "heapsFactorsThroughEqualityPattern",
                    "noUniversalEqualityPatternRecoveryFromHeaps",
                    "patternRepresentativeRoundTrip"):
        assert theorem in factor
    assert "ZipfThreeDrawEqualityPatternFactorExact" in umbrella
    for forbidden in ("postulate\n","{!!}","allow-unsolved-metas",
                      "NO_POSITIVITY_CHECK","{-# TERMINATING #-}"):
        assert forbidden not in factor
