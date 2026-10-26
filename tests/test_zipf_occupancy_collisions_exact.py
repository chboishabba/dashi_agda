"""Independent finite enumeration checks for conditional occupancy moments."""
from fractions import Fraction as F
from itertools import product,permutations
from math import prod
from pathlib import Path
import sys
import pytest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import zipf_occupancy_collisions_exact as C
from zipf_heaps_bridge import expected_iid_vocabulary,expected_permutation_vocabulary,finite_rank_probabilities

def iid_ensemble(p,n):
    return [(word,prod(p[i] for i in word)) for word in product(range(len(p)),repeat=n)]

def variance_by_enumeration(outcomes):
    mean=sum((len(set(word))*mass for word,mass in outcomes),F())
    return sum(((len(set(word))-mean)**2*mass for word,mass in outcomes),F())

def test_iid_two_draw_identity_normalized_zipf():
    for k in range(1,6):
        for s in (0,1,2,3):
            for q in (0,1,2):
                p=finite_rank_probabilities(k,s,q)
                assert C.iid_two_draw_vocabulary(p)==expected_iid_vocabulary(p,2)
                assert C.iid_collision_probability(p)==sum((x*x for x in p),F())

def test_iid_three_draw_identity_exact():
    for p in ((F(1),),(F(1,2),F(1,2)),(F(1,2),F(1,3),F(1,6))):
        assert C.iid_three_draw_vocabulary(p)==expected_iid_vocabulary(p,3)

def test_iid_discrete_second_difference_exact_negative():
    p=finite_rank_probabilities(5,2,1)
    for n in range(15):
        delta=(expected_iid_vocabulary(p,n+2)
                -2*expected_iid_vocabulary(p,n+1)+expected_iid_vocabulary(p,n))
        assert delta==C.iid_novelty_second_difference(p,n)
        assert delta<0

def test_iid_variance_independent_exhaustive_enumeration():
    for p in ((F(1),),(F(1,2),F(1,2)),(F(1,2),F(1,3),F(1,6))):
        for n in range(5):
            ensemble=iid_ensemble(p,n)
            assert sum((mass for _,mass in ensemble),F())==1
            assert C.iid_vocabulary_variance(p,n)==variance_by_enumeration(ensemble)

def test_permutation_variance_independent_exhaustive_enumeration():
    for counts in ((1,1),(2,2),(3,2,1),(1,2,1)):
        words=set(permutations(tuple(i for i,f in enumerate(counts) for _ in range(f))))
        for n in range(sum(counts)+1):
            ensemble=[(w[:n],F(1,len(words))) for w in words]
            assert C.permutation_vocabulary_variance(counts,n)==variance_by_enumeration(ensemble)

def test_iid_variance_is_bounded_by_mean_exact():
    for k in range(1,7):
        for s in (0,1,3):
            p=finite_rank_probabilities(k,s)
            for n in range(13):
                assert 0<=C.iid_vocabulary_variance(p,n)<=C.iid_variance_upper_bound(p,n)

def test_permutation_two_draw_collision_exact():
    for counts in ((1,1),(2,2,2),(3,2,1),(8,)):
        assert C.permutation_two_draw_vocabulary(counts)==expected_permutation_vocabulary(counts,2)

def test_replacement_gap_exact_positive_for_multiple_types():
    assert C.two_draw_without_vs_with_replacement_gap((2,2,2))==F(2,15)
    assert C.two_draw_without_vs_with_replacement_gap((5,))==0
    assert C.two_draw_without_vs_with_replacement_gap((3,2,1))>0

def test_simpson_effective_count_and_uniform_bound():
    assert C.iid_effective_type_count((F(1,4),)*4)==4
    assert C.iid_effective_type_count((F(1),F(0),F(0)))==1
    assert C.exact_uniform_collision_bound((F(1,4),)*4)==(F(1,4),F(1))
    assert C.iid_collision_probability((F(3,4),F(1,4)))>F(1,2)

def test_conditioning_is_hypothesis_not_automatic():
    with pytest.raises(ValueError): C.permutation_collision_probability((1,))
    with pytest.raises(ValueError): C.iid_collision_probability((F(1,2),))
    with pytest.raises(ValueError): C.iid_vocabulary_variance((F(1),),-1)
    with pytest.raises(ValueError): C.permutation_vocabulary_variance((2,2),5)
