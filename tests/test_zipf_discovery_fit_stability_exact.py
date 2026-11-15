"""Exact coupling bounds and rare-tail non-uniform sensitivity tests."""
from fractions import Fraction as F
from itertools import product
from math import comb
from pathlib import Path
import sys
import pytest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from zipf_discovery_fit_stability_exact import (
    iid_prefix_total_variation_bound,
    permutation_prefix_total_variation_bound,
    completion_event_stability_certificate,
    rare_tail_unstable_completion_witness,
)
from zipf_completion_time_exact import completion_cdf


def test_iid_maximal_coupling_bound_matches_exact_one_step_tv():
    for p,q in (((F(1,2),F(1,2)),(F(2,3),F(1,3))),
                ((F(1,4),F(3,4)),(F(3,4),F(1,4))),
                ((F(1),F(0)),(F(0),F(1)))):
        tv=sum((abs(x-y) for x,y in zip(p,q)),F())/2
        assert iid_prefix_total_variation_bound(p,q,0)==0
        assert iid_prefix_total_variation_bound(p,q,1)==tv
        for t in range(10):
            assert iid_prefix_total_variation_bound(p,q,t)==1-(1-tv)**t


def test_permutation_exact_shared_position_coupling_formula():
    for f,g in (((3,1),(2,2)),((4,1,1),(2,2,2)),((9,7,3,1),(9,7,2,2))):
        n=sum(f)
        d=sum(abs(x-y) for x,y in zip(f,g))//2
        for t in range(n+1):
            assert permutation_prefix_total_variation_bound(f,g,t)==1-F(comb(n-d,t),comb(n,t))


def test_any_two_finite_histograms_completion_event_is_bounded():
    for k in (2,3):
        choices=list(product((1,2,3),repeat=k))
        for f in choices:
            for g in choices:
                if sum(f)!=sum(g):continue
                for t in range(sum(f)+1):
                    receipt=completion_event_stability_certificate(f,g,t)
                    for sampler in ('iid','permutation'):
                        gap,bound=receipt[sampler]
                        assert gap<=bound
                        assert gap==abs(completion_cdf(f,t,sampler)-completion_cdf(g,t,sampler))


def test_identity_and_incomplete_support_conventions():
    for sampler in ('iid','permutation'):
        assert completion_event_stability_certificate((2,1),(2,1),2)[sampler]==(F(),F())
    with pytest.raises(ValueError):completion_event_stability_certificate((2,1),(3,1),2)
    with pytest.raises(ValueError):permutation_prefix_total_variation_bound((2,1),(2,1),4)
    with pytest.raises(ValueError):iid_prefix_total_variation_bound((F(1),), (F(1,2),F(1,2)),1)
    with pytest.raises(ValueError):iid_prefix_total_variation_bound((F(1,2),F(1,2)),(F(1,2),F(1,2)),True)
    with pytest.raises(ValueError):rare_tail_unstable_completion_witness(1)


def test_tail_obstruction_shrinks_tv_while_mean_ratio_explodes():
    prev_tv=F(1)
    for m in (2,3,4,6,10,20,40):
        tv,ea,eb,ratio=rare_tail_unstable_completion_witness(m)
        assert tv<prev_tv
        assert ratio>F(m,2)
        assert ea>eb
        prev_tv=tv


def test_tiny_tv_keeps_fixed_t_completion_event_difference_small():
    for m in (10,20,40):
        n=m*m
        f,g=(n-1,1),(n-m,m)
        for t in (1,2,3):
            gap,bound=completion_event_stability_certificate(f,g,t)['iid']
            assert gap<=bound<=t*F(m-1,n)
