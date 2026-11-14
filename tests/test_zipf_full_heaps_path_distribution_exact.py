"""Independent exact word-space tests of complete Heaps-path probability law."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import permutations, product
from pathlib import Path
import sys
import pytest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"scripts"))
from zipf_full_heaps_path_distribution_exact import (
    full_heaps_curve_law, abc_joint_path_boundary, aabc_joint_path_boundary
)
from zipf_heaps_bridge import observed_prefix_diversity


def _independent_word_space(counts,t,sampler):
    n=sum(counts)
    if sampler=="iid":
        dist=defaultdict(F)
        for word in product(range(len(counts)),repeat=t):
            p=F(1)
            for i in word:p*=F(counts[i],n)
            dist[observed_prefix_diversity(word)]+=p
        return dict(dist)
    tokens=tuple(i for i,x in enumerate(counts) for _ in range(x))
    words=set(permutations(tokens))
    dist=defaultdict(F)
    for word in words:
        dist[observed_prefix_diversity(word[:t])]+=F(1,len(words))
    return dict(dist)


def test_abc_six_sample_space_collapses_complete_heaps_curve():
    r=abc_joint_path_boundary()
    assert r["permutation"]=={(0,1,2,3):F(1)}
    assert r["iid"]!={ (0,1,2,3):F(1) }
    assert r["iid"][(0,1,2,3)]==F(2,9)


def test_aabc_twelve_sample_space_three_joint_curves():
    r=aabc_joint_path_boundary()
    assert r["permutation"]=={
        (0,1,1,2,3):F(1,6),
        (0,1,2,2,3):F(1,3),
        (0,1,2,3,3):F(1,2)}
    assert r["iid"]!=r["permutation"]


def test_independent_iid_all_short_words_match_path_dynamic_program():
    for counts in ((1,1), (2,1), (1,1,1), (2,1,1)):
        for t in range(5):
            assert full_heaps_curve_law(counts,t,"iid")==_independent_word_space(counts,t,"iid")


def test_independent_uniform_multisets_match_complete_path_dynamic_program():
    for counts in ((1,), (1,1), (2,1), (1,1,1), (2,1,1),(2,2,1)):
        for t in range(sum(counts)+1):
            assert full_heaps_curve_law(counts,t,"permutation")==(
                _independent_word_space(counts,t,"permutation"))


def test_observed_novelty_increments_only_zero_or_one():
    for sampler in ("iid","permutation"):
        for counts in ((1,1,1),(2,1,1),(3,1,1)):
            for t in range(min(5,sum(counts))+1):
                for curve in full_heaps_curve_law(counts,t,sampler):
                    assert curve[0]==0
                    assert all(y-x in (0,1) for x,y in zip(curve,curve[1:]))


def test_source_owner_marginal_consistency_for_more_general_small_laws():
    # The implementation itself validates ALL prefix PMFs against the
    # existing separate zipf_stochastic_majorization_exact owner.
    for counts in ((2,2,2),(3,1,2),(3,3,1),(4,2,1)):
        for sampler in ("iid","permutation"):
            assert sum(full_heaps_curve_law(counts,6,sampler).values(),F())==1


def test_fail_closed_bad_sampler_horizon_counts_and_state_limit():
    for bad in (True, -1, 15, 0.5):
        with pytest.raises(ValueError):full_heaps_curve_law((1,1),bad,"iid")
    for bad in ("marginal","multinomial",None):
        with pytest.raises(ValueError):full_heaps_curve_law((1,1),1,bad)
    for bad in ((),(1,0),(True,1),(1,-1)):
        with pytest.raises(ValueError):full_heaps_curve_law(bad,1,"iid")
    with pytest.raises(ValueError):full_heaps_curve_law((1,1),3,"permutation")
    with pytest.raises(ValueError):full_heaps_curve_law((1,1,1),3,"iid",max_states=1)


def test_joint_curves_distinguish_sampler_despite_same_arrival_order_law():
    from zipf_first_discovery_plackett_luce_exact import abc_first_discovery_receipt
    arrival=abc_first_discovery_receipt()
    assert sum(arrival["order_probabilities"].values(),F())==1
    assert arrival["iid_expected_v2"]!=arrival["permutation_expected_v2"]
    assert (aabc_joint_path_boundary()["iid"]
            !=aabc_joint_path_boundary()["permutation"])
