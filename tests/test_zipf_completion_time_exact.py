"""Independent exact audit for two-sampler coupon completion / rare tail."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from math import comb
from pathlib import Path
import sys
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from zipf_completion_time_exact import (
    completion_cdf, completion_mean, completion_tail_bounds,
    majorization_completion_certificate,
)
from zipf_heaps_bridge import multiset_count_majorizes


def _exhaustive_cdf(counts, t, sampler):
    n = sum(counts)
    if sampler == 'iid':
        total = F()
        for word in product(range(len(counts)), repeat=t):
            if len(set(word)) == len(counts):
                probability = F(1)
                for i in word: probability *= F(counts[i], n)
                total += probability
        return total
    labels = tuple(i for i, f in enumerate(counts) for _ in range(f))
    return F(sum(len({labels[i] for i in indices}) == len(counts)
                 for indices in combinations(range(n), t)), comb(n, t))


def test_exact_cdf_matches_independent_full_sample_space_enumeration():
    for c in ((1,), (1,1), (2,1), (1,2,1), (2,2,1), (3,1,1)):
        for t in range(sum(c)+1):
            for sampler in ('iid','permutation'):
                assert completion_cdf(c,t,sampler) == _exhaustive_cdf(c,t,sampler)


def test_iid_large_horizon_and_single_type_are_correct():
    for sampler in ('iid','permutation'):
        assert completion_cdf((8,),0,sampler) == 0
        assert completion_cdf((8,),1,sampler) == 1
        assert completion_mean((8,),sampler) == 1
    assert completion_cdf((2,1),10,'iid') == 1 - F(2,3)**10 - F(1,3)**10
    assert completion_cdf((2,1),2,'permutation') == F(2,3)
    assert completion_cdf((2,1),3,'permutation') == 1


def test_exact_completion_means_independent_tail_sums():
    for c in ((1,), (1,1), (2,1), (3,1), (2,2), (2,1,1)):
        n = sum(c)
        mean_permutation = sum((1 - _exhaustive_cdf(c,t,'permutation')
                                for t in range(n)), F())
        assert completion_mean(c,'permutation') == mean_permutation
        # IID tail sum to finite t is a strict lower bound, and its
        # exact remainder is independently summed by the geometric formula
        # over nonempty excluded-type sets.
        horizon = 16
        finite = sum((1 - _exhaustive_cdf(c,t,'iid') for t in range(6)),F())
        assert finite <= completion_mean(c,'iid')
        if len(c)==2:
            a,b=c
            expected=F(n,a)+F(n,b)-1
            assert completion_mean(c,'iid') == expected


def test_expected_values_concentrated_two_type_examples():
    assert completion_mean((3,1),'iid') == F(13,3)
    assert completion_mean((2,2),'iid') == 3
    assert completion_mean((3,1),'permutation') == F(11,4)
    assert completion_mean((2,2),'permutation') == F(7,3)


def test_bounds_and_majorization_every_time_up_to_finite_sample():
    for k in (2,3,4):
        candidates=list(product((1,2,3),repeat=k))
        for c in candidates:
            for t in range(sum(c)+1):
                for sampler in ('iid','permutation'):
                    lo, actual, hi = completion_tail_bounds(c,t,sampler)
                    assert lo <= actual <= hi
                    assert actual == 1-completion_cdf(c,t,sampler)
            for d in candidates:
                if sum(c)!=sum(d) or not multiset_count_majorizes(c,d):
                    continue
                for t in range(sum(c)+1):
                    rec = majorization_completion_certificate(c,d,t)
                    for sampler in ('iid','permutation'):
                        ca,cb,ea,eb=rec[sampler]
                        assert ca<=cb and ea>=eb


def test_iid_order_beyond_end_of_original_multiset():
    for concentrated,dispersed in (((3,1),(2,2)), ((4,1,1),(2,2,2))):
        for t in (10,20,50):
            result=majorization_completion_certificate(concentrated,dispersed,t)
            assert result['iid'][0] <= result['iid'][1]
            assert result['permutation'][0] == result['permutation'][1] == 1


def test_domain_and_source_types_fail_closed():
    for invalid in ((),(2,0),(True,2),(1,-1)):
        with pytest.raises(ValueError):completion_cdf(invalid,0,'iid')
    for invalid_sampler in ('bootstrap','IID','shuffle',None):
        with pytest.raises(ValueError):completion_mean((2,1),invalid_sampler)
    for invalid_draws in (True,-1,F(1,2)):
        with pytest.raises(ValueError):completion_cdf((2,1),invalid_draws,'iid')
    with pytest.raises(ValueError):completion_cdf((2,1),4,'permutation')
    with pytest.raises(ValueError):completion_mean((1,)*19,'iid')
    with pytest.raises(ValueError):majorization_completion_certificate((2,2),(3,1),2)
    with pytest.raises(ValueError):majorization_completion_certificate((2,1),(2,1),-1)


def _independent_iid_expected_time(counts):
    """Exact first-step dynamic program on already-seen type subsets."""
    n=sum(counts)
    memo={ (1 << len(counts))-1: F(0) }
    def rec(mask):
        if mask in memo: return memo[mask]
        seen=sum(counts[i] for i in range(len(counts)) if mask & (1<<i))
        remaining=F(n-seen,n)
        value=F(1)
        for i,frequency in enumerate(counts):
            if not (mask & (1<<i)):
                value += F(frequency,n)*rec(mask | (1<<i))
        memo[mask]=value/remaining
        return memo[mask]
    return rec(0)


def test_iid_expected_time_matches_independent_absorbing_chain():
    for k in range(1,5):
        for c in product((1,2,3),repeat=k):
            assert completion_mean(c,'iid') == _independent_iid_expected_time(c)


def test_permutation_expected_time_matches_exhaustive_label_orders():
    from itertools import permutations
    for c in ((1,1),(2,1),(2,2),(2,1,1)):
        labels=tuple(i for i,f in enumerate(c) for _ in range(f))
        times=[]
        for word in permutations(labels):
            seen=set()
            for t,x in enumerate(word,1):
                seen.add(x)
                if len(seen)==len(c):
                    times.append(t)
                    break
        assert completion_mean(c,'permutation') == F(sum(times),len(times))
