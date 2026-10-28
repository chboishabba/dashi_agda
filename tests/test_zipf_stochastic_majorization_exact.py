"""Independent exact finite stochastic-dominance and sampler-disambiguation tests."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from math import comb
from pathlib import Path
import sys
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from zipf_stochastic_majorization_exact import (
    distinct_count_pmf, upper_tails, discovery_stochastic_majorization_certificate,
)
from zipf_heaps_bridge import multiset_count_majorizes


def _independent_iid_enumeration(counts, t):
    n = sum(counts)
    outcomes = defaultdict(F)
    for word in product(range(len(counts)), repeat=t):
        weight = F(1)
        for rank in word:
            weight *= F(counts[rank], n)
        outcomes[len(set(word))] += weight
    return tuple(outcomes[j] for j in range(len(counts)+1))


def _independent_without_replacement_enumeration(counts, t):
    labels = tuple(i for i, count in enumerate(counts) for _ in range(count))
    outcomes = defaultdict(int)
    for indices in combinations(range(len(labels)), t):
        outcomes[len({labels[i] for i in indices})] += 1
    return tuple(F(outcomes[j], comb(len(labels), t)) for j in range(len(counts)+1))


def test_exact_coefficients_equal_independent_exhaustive_sample_spaces():
    for c in ((1,), (1,1), (2,1), (1,2,1), (2,2,1), (3,1,1)):
        for t in range(sum(c)+1):
            assert distinct_count_pmf(c,t,'iid') == _independent_iid_enumeration(c,t)
            assert distinct_count_pmf(c,t,'permutation') == _independent_without_replacement_enumeration(c,t)


def test_majorization_stochastically_orders_every_threshold_and_prefix():
    for k in (2,3,4):
        candidates = list(product((1,2,3),repeat=k))
        for f in candidates:
            for g in candidates:
                if sum(f)!=sum(g) or not multiset_count_majorizes(f,g):
                    continue
                for t in range(sum(f)+1):
                    tables = discovery_stochastic_majorization_certificate(f,g,t)
                    for sampler in ('iid','permutation'):
                        a,b = tables[sampler]
                        assert len(a)==len(b)==k+1
                        assert a[0]==b[0]==1
                        assert all(x<=y for x,y in zip(a,b))


def test_strict_tail_dominance_and_variance_nonordering_coexist():
    # An existing regression has opposite variance signs at different times.
    concentrated, dispersed = (3,1),(2,2)
    for t in (2,3):
        result = discovery_stochastic_majorization_certificate(concentrated,dispersed,t)
        for sampler in ('iid','permutation'):
            a,b = result[sampler]
            assert a[2] <= b[2]
        assert result['iid'][0][2] < result['iid'][1][2]


def test_tail_probability_not_derived_from_mean_alone():
    # Equal means but distinct PMFs are possible, so run full distribution tests.
    assert distinct_count_pmf((1,1), 1, 'iid') == (F(0),F(1),F(0))
    assert distinct_count_pmf((1,1), 1, 'permutation') == (F(0),F(1),F(0))
    assert distinct_count_pmf((1,1), 2, 'iid') == (F(0),F(1,2),F(1,2))
    assert distinct_count_pmf((1,1), 2, 'permutation') == (F(0),F(0),F(1))


def test_single_type_and_large_iid_horizon():
    assert distinct_count_pmf((3,), 25, 'iid') == (F(0),F(1))
    assert distinct_count_pmf((3,), 3, 'permutation') == (F(0),F(1))


def test_fail_closed_wrong_horizon_sampler_counts_and_relation():
    for x in (True, -1, 1.5):
        with pytest.raises(ValueError):distinct_count_pmf((2,1),x,'iid')
    for c in ((1,0),(2,False),(),(1,-2)):
        with pytest.raises(ValueError):distinct_count_pmf(c,0,'iid')
    with pytest.raises(ValueError):distinct_count_pmf((2,1),4,'permutation')
    with pytest.raises(ValueError):distinct_count_pmf((2,1),2,'unknown')
    with pytest.raises(ValueError):discovery_stochastic_majorization_certificate((2,2),(3,1),2)
    with pytest.raises(ValueError):discovery_stochastic_majorization_certificate((2,1),(2,2),2)
    with pytest.raises(ValueError):discovery_stochastic_majorization_certificate((2,1),(2,1),4)
    with pytest.raises(ValueError):upper_tails((F(1,2), F(1,3)))



def test_pair_cdf_exact_against_independent_two_type_enumeration():
    from zipf_stochastic_majorization_exact import pair_second_type_cdf
    for a,b in ((1,1),(2,1),(3,2),(4,3)):
        for t in range(a+b+1):
            # Both distinct if exactly two type labels have appeared.
            ii = _independent_iid_enumeration((a,b),t)[2]
            pp = _independent_without_replacement_enumeration((a,b),t)[2]
            assert pair_second_type_cdf(a,b,t,'iid') == ii
            assert pair_second_type_cdf(a,b,t,'permutation') == pp


def test_same_quantile_couples_all_prefixes_for_each_one_token_transfer():
    from zipf_stochastic_majorization_exact import pair_pathwise_quantile_certificate
    for a in range(2,7):
        for b in range(2,a+1):
            for sampler in ('iid','permutation'):
                witnesses = pair_pathwise_quantile_certificate(a,b,a+b,sampler)
                assert witnesses
                assert all(tc>=td for _,tc,td in witnesses)
                assert all(F(0)<u<F(1) for u,_,_ in witnesses)
    with pytest.raises(ValueError):pair_pathwise_quantile_certificate(1,2,2,'iid')
    with pytest.raises(ValueError):pair_pathwise_quantile_certificate(2,2,5,'permutation')
