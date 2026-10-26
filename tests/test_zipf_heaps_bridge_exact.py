"""Mathematical finite bridge certificates and independence no-go tests."""
from fractions import Fraction as F
from itertools import permutations
from pathlib import Path
import sys
import pytest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import zipf_heaps_bridge as H


def test_exact_finite_pmf_and_shifted_zero_and_uniform():
    assert H.finite_rank_probabilities(3, 1) == (F(6,11),F(3,11),F(2,11))
    assert H.finite_rank_probabilities(4, 0, 2) == (F(1,4),)*4
    assert sum(H.finite_rank_probabilities(5, 3, 2)) == 1


def test_exact_cdf_quantile_and_moment_on_attained_mass():
    p = H.finite_rank_probabilities(3, 1)
    assert H.finite_cdf(p) == (F(6,11), F(9,11), F(1))
    assert H.finite_quantile(p, F(6,11)) == 1
    assert H.finite_quantile(p, F(6,11)+F(1,110)) == 2
    assert H.finite_quantile(p, F(1)) == 3
    assert H.finite_rank_moment(p, 0)==1
    assert H.finite_rank_moment(p, 1)==F(18,11)
    assert H.finite_rank_moment(p, 2)==F(36,11)


def test_finite_probability_parameter_domain_gates():
    with pytest.raises(ValueError): H.finite_rank_probabilities(0,1)
    with pytest.raises(ValueError): H.finite_rank_probabilities(2,-1)
    with pytest.raises(ValueError): H.finite_quantile((F(1),),F(0))
    with pytest.raises(ValueError): H.expected_iid_vocabulary([F(1,2)],3)
    with pytest.raises(ValueError): H.expected_permutation_vocabulary((1,2),4)


def test_iid_heaps_first_values_and_discrete_derivative():
    p = H.finite_rank_probabilities(3, 0)
    assert H.expected_iid_vocabulary(p,0) == 0
    assert H.expected_iid_vocabulary(p,1) == 1
    assert H.expected_iid_vocabulary(p,3) == F(19,9)
    for n in range(6):
        assert H.expected_iid_vocabulary(p,n+1)-H.expected_iid_vocabulary(p,n) == H.expected_iid_new_type(p,n)
        assert 0 < H.expected_iid_new_type(p,n+1) < H.expected_iid_new_type(p,n)


def test_temporal_permutation_model_differs_from_iid_with_same_marginals():
    counts=(2,2,2)
    p=(F(1,3),)*3
    assert H.expected_permutation_vocabulary(counts,3)==F(12,5)
    assert H.expected_iid_vocabulary(p,3)==F(19,9)
    assert H.expected_permutation_vocabulary(counts,6)==3
    assert H.expected_iid_vocabulary(p,6)<3


def test_exact_sharp_envelope_exhaustion_three_types():
    counts=(3,2,1)
    all_strings=set(permutations('aaabbc'))
    assert len(all_strings)==60
    for t in range(7):
        observed=[len(set(s[:t])) for s in all_strings]
        assert H.distinct_envelope(counts,t)==(min(observed),max(observed))


def test_witness_same_histogram_but_different_heaps_prefix():
    a='aabbcc';b='abcabc'
    assert sorted(a)==sorted(b)
    assert len(set(a[:3]))==2
    assert len(set(b[:3]))==3
    assert H.distinct_envelope((2,2,2),3)==(2,3)


def test_same_unigram_rank_different_exact_block_entropy():
    iid_unigram=(F(1,2),F(1,2))
    persistent_unigram=(F(1,2),F(1,2))
    assert iid_unigram==persistent_unigram
    assert H.dyadic_block_entropy(iid_unigram)==1
    assert H.dyadic_block_entropy((F(1,4),)*4)==2
    assert H.dyadic_block_entropy((F(1,2),F(0),F(0),F(1,2)))==1
    with pytest.raises(ValueError): H.dyadic_block_entropy((F(1,3),)*3)


def test_exact_hypergeometric_endpoints_and_singleton_limits():
    assert H.expected_permutation_vocabulary((1,2,4),0)==0
    assert H.expected_permutation_vocabulary((1,2,4),1)==1
    assert H.expected_permutation_vocabulary((1,2,4),7)==3
    assert H.distinct_envelope((1,2,4),7)==(3,3)


def test_zero_drawing_preserves_empty_vocabulary_not_empty_model():
    assert H.expected_iid_vocabulary((F(1),),0)==0
    assert H.expected_iid_vocabulary((F(1),),5)==1
    assert H.expected_iid_new_type((F(1),),1)==0


def test_noninjectivity_of_histogram_to_timing_is_independent_of_zipf_fit():
    a='aaaaabbbbb'; b='ababababab'
    assert sorted(a)==sorted(b)
    assert tuple(len(set(a[:i])) for i in range(1,len(a)+1)) != tuple(len(set(b[:i])) for i in range(1,len(b)+1))


def test_derived_finite_urn_limit_as_draws_increase():
    p=H.finite_rank_probabilities(6,3,2)
    for draws in (0,1,2,5,10,100):
        e=H.expected_iid_vocabulary(p,draws)
        assert 0 <= e <= len(p)
    assert H.expected_iid_vocabulary(p,1000) > F(59,10)
