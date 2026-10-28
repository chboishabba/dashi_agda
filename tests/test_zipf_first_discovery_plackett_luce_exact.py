"""First-discovery order parity: original Plackett-Luce, independent samplers."""
from collections import Counter
from fractions import Fraction as F
from itertools import permutations, product
from pathlib import Path
import sys
import pytest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"scripts"))
from zipf_first_discovery_plackett_luce_exact import (
    first_seen_type_order, size_biased_order_law,
    iid_next_novel_type_probability, uniform_multiset_first_seen_order_law,
    first_discovery_two_sampler_certificate, abc_first_discovery_receipt,
)


def _independent_first_seen(word):
    result=[]
    for letter in word:
        if letter not in result: result.append(letter)
    return tuple(result)


def test_aabc_exact_first_discovery_order_law_and_timing_difference():
    r=abc_first_discovery_receipt()
    assert r["order_probabilities"] == {
        "ABC":F(1,4),"ACB":F(1,4),
        "BAC":F(1,6),"BCA":F(1,12),
        "CAB":F(1,6),"CBA":F(1,12),
    }
    assert r["iid_expected_v2"] == F(13,8)
    assert r["permutation_expected_v2"] == F(11,6)
    assert r["iid_expected_v2"] != r["permutation_expected_v2"]


def test_uniform_abc_all_six_order_probabilities_identical():
    r=first_discovery_two_sampler_certificate((1,1,1))
    for law in r.values():
        assert len(law)==6 and set(law.values())=={F(1,6)}


def test_all_small_k2_k3_histograms_match_exhaustive_permutation():
    # Independent physical-word enumeration is separate from the PL model.
    for k in (2,3):
        for counts in product((1,2,3),repeat=k):
            if sum(counts)>9:continue
            result=first_discovery_two_sampler_certificate(counts)
            assert result["plackett_luce"]==result["iid_first_discovery"]
            assert result["plackett_luce"]==result["uniform_permutation_first_discovery"]


def test_size_biased_law_agrees_with_independent_label_multiset_counting():
    for counts in ((1,1,1),(2,1,1),(3,1,1),(2,2,1),(1,2,3)):
        tokens=tuple(i for i,f in enumerate(counts) for _ in range(f))
        words=set(permutations(tokens))
        empirical=Counter(_independent_first_seen(word) for word in words)
        independent={order:F(n,len(words)) for order,n in empirical.items()}
        assert independent==size_biased_order_law(counts)
        assert independent==uniform_multiset_first_seen_order_law(counts)


def test_iid_geometric_next_new_type_probability():
    c=(4,2,1)
    assert iid_next_novel_type_probability(c,(),0)==F(4,7)
    assert iid_next_novel_type_probability(c,(0,),1)==F(2,3)
    assert iid_next_novel_type_probability(c,(0,),2)==F(1,3)
    assert iid_next_novel_type_probability(c,(1,0),2)==1


def test_first_appearance_order_observable_is_not_full_prefix_curve():
    # Same first-discovery type order ABC, distinct discovery times.
    x=(0,1,2,0)
    y=(0,0,1,2)
    assert first_seen_type_order(x)==first_seen_type_order(y)==(0,1,2)
    from zipf_heaps_bridge import observed_prefix_diversity
    assert observed_prefix_diversity(x)!=(observed_prefix_diversity(y))


def test_no_hidden_iid_or_empirical_provenance_promotion():
    # A byte-equal histogram alone does not assert IID or exchangeability.
    for invalid in ((0,),(-1,1),(True,2),(),(1.5,2)):
        with pytest.raises(ValueError):size_biased_order_law(invalid)
    with pytest.raises(ValueError):uniform_multiset_first_seen_order_law((10,1))
    with pytest.raises(ValueError):iid_next_novel_type_probability((2,1),(0,),0)
    with pytest.raises(ValueError):iid_next_novel_type_probability((2,1),(0,0),1)
    with pytest.raises(ValueError):first_seen_type_order((0,-1))


def test_statistical_source_reuses_explicit_abc_six_owner_and_credits_prior_art():
    src=(ROOT/"scripts/zipf_first_discovery_plackett_luce_exact.py").read_text()
    assert "from zipf_abc_six_order_receipt import ABC_ORDERS" in src
    assert "Plackett" in src and "Luce" in src
    assert "first_discovery_two_sampler_certificate" in src
    assert "IID" in src and "permutation" in src
