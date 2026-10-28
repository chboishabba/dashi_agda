"""Independent exact tests of Schur-concave vocabulary expectation."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import sys
import pytest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import zipf_majorization_expected_heaps_exact as M
from zipf_heaps_bridge import (
    expected_iid_vocabulary, expected_permutation_vocabulary,
    multiset_count_majorizes,
)


def test_every_majorized_count_pair_has_two_sampler_monotonicity():
    for k in (2, 3, 4):
        histograms = list(product((1, 2, 3), repeat=k))
        for a in histograms:
            for b in histograms:
                if sum(a) != sum(b) or not multiset_count_majorizes(a, b):
                    continue
                for t in range(sum(a)+1):
                    (ia, ib), (pa, pb) = M.majorization_expected_vocabulary_certificate(a, b, t)
                    assert ia <= ib and pa <= pb
                    assert ia == expected_iid_vocabulary(tuple(F(x,sum(a)) for x in a),t)
                    assert pa == expected_permutation_vocabulary(a,t)


def test_one_token_transfer_nonnegative_loss_all_prefixes():
    for c in ((4, 2, 1), (5, 3, 2), (3, 3, 2, 1), (7, 4)):
        for i,a in enumerate(c):
            for j,b in enumerate(c):
                if i == j or a < b or b < 2: continue
                d = M.transfer_one_token_to_larger_type(c,i,j)
                assert sum(d) == sum(c)
                for t in range(sum(c)+1):
                    iid, perm = M.one_transfer_expected_loss(c,i,j,t)
                    assert iid >= 0 and perm >= 0
                    # Adjacent one-token loss equals marginal difference.
                    ai, ap = M.local_one_step_presence_gain(sum(c), a, t)
                    bi, bp = M.local_one_step_presence_gain(sum(c), b-1, t)
                    assert iid == bi-ai
                    assert perm == bp-ap


def test_discrete_presence_gain_is_nonincreasing():
    for N in range(1, 13):
        for n in range(N+1):
            gains=[M.local_one_step_presence_gain(N,k,n) for k in range(N)]
            assert all(x[0]>=y[0] and x[1]>=y[1] for x,y in zip(gains,gains[1:]))


def test_inequality_can_be_strict_but_has_mean_equalities_at_endpoints():
    more=(6,2,1); less=(3,3,3)
    for t in range(10):
        (a,b),(c,d)=M.majorization_expected_vocabulary_certificate(more,less,t)
        if t==0:
            assert a==b==c==d==0
        if t==1:
            assert a==b==c==d==1
        if t==9:
            assert c==d==3  # Without replacement, all types seen.
        if t in (2,3):
            assert a<b and c<d


def test_zipf_exponent_majorizes_for_all_small_integer_shapes():
    for k in range(1, 8):
        for q in range(4):
            for low in range(5):
                for high in range(low, 6):
                    p0,p1=M.zipf_shape_majorization_certificate(k,low,high,q)
                    assert len(p0)==len(p1)==k
                    for draws in (0,1,2,3,8):
                        x,y=M.zipf_exponent_iid_heaps_certificate(k,low,high,q,draws)
                        assert x<=y


def test_zero_uncertainty_and_noncomparable_arguments_fail_closed():
    for c,r,p in (((1,1),0,1),((1,4),0,1),((3,1),0,1),((3,2),1,1)):
        with pytest.raises(ValueError):M.transfer_one_token_to_larger_type(c,r,p)
    with pytest.raises(ValueError):M.majorization_expected_vocabulary_certificate((5,2,2),(4,4,1),2)
    with pytest.raises(ValueError):M.majorization_expected_vocabulary_certificate((3,2),(3,1),2)
    with pytest.raises(ValueError):M.zipf_shape_majorization_certificate(5,2,1)
    with pytest.raises(ValueError):M.zipf_exponent_iid_heaps_certificate(5,1,2,0,-1)
    with pytest.raises(ValueError):M.local_one_step_presence_gain(5,5,1)
