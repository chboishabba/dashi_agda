"""Exact finite distribution over the ENTIRE prefix-discovery curve.

Existing owners reused:
  zipf_heaps_bridge._validated_counts / expected_*_vocabulary;
  zipf_stochastic_majorization_exact.distinct_count_pmf (one-time marginal).
This code supplies a new joint-path observable, not a duplicate probability
carrier or a claim of universal empirical Zipf time-dependence.

Under IID, each draw uses fixed c_i/N with replacement.
Under permutation, draw c_i remaining physical tokens out of N-left.
The two random processes have different distributions over full Heaps
histories, even though their first-appearance label-order law agrees
(Plackett 1975 / Luce 1959, separately attributed).
New bounded exact adapter: Johl Brown + OpenAI ChatGPT, 2026-10-28.
Python exact checking != Agda kernel proof.
"""
from __future__ import annotations

from collections import defaultdict
from fractions import Fraction
from typing import Literal, Sequence

from zipf_heaps_bridge import (
    _validated_counts, expected_iid_vocabulary, expected_permutation_vocabulary
)
from zipf_stochastic_majorization_exact import distinct_count_pmf

Sampler = Literal["iid","permutation"]


def full_heaps_curve_law(
    counts: Sequence[int], draws: int, sampler: Sampler,
    max_states: int = 120000
) -> dict[tuple[int,...], Fraction]:
    """Exact PMF over all FULL prefix V_0,...,V_t curves.

    Complexity is exponential in the number of novelty-event histories;
    fail closed at t>14 or excessive states. The theorem's mathematical
    scope is not restricted by this executable resource limit.
    """
    c=_validated_counts(counts)
    n=sum(c)
    if (type(draws) is not int or draws<0 or draws>14
            or sampler not in ("iid","permutation")
            or (sampler=="permutation" and draws>n)
            or type(max_states) is not int or max_states<1):
        raise ValueError("valid sampler, horizon<=14, nonzero state budget")
    # State (remaining counts, discovered-type mask, full prefix curve).
    states={(c,0,(0,)):Fraction(1)}
    for step in range(draws):
        nxt=defaultdict(Fraction)
        for (remaining,mask,curve),weight in states.items():
            denominator=n if sampler=="iid" else n-step
            for i in range(len(c)):
                amount=c[i] if sampler=="iid" else remaining[i]
                if not amount:continue
                next_remaining=remaining
                if sampler=="permutation":
                    next_remaining=tuple(x-1 if j==i else x
                                         for j,x in enumerate(remaining))
                next_mask=mask | (1<<i)
                next_curve=curve+(next_mask.bit_count(),)
                nxt[(next_remaining,next_mask,next_curve)]+=(
                    weight*Fraction(amount,denominator))
        if len(nxt)>max_states:
            raise ValueError("explicit exact full-history state budget exceeded")
        states=nxt
    dist=defaultdict(Fraction)
    for (_,_,curve),prob in states.items():
        dist[curve]+=prob
    law=dict(sorted(dist.items()))
    assert sum(law.values(),Fraction())==1
    assert all(p>0 and len(curve)==draws+1 and curve[0]==0
               for curve,p in law.items())

    # Independent marginal owner verification at every t≤draws.
    for t in range(draws+1):
        calculated=tuple(sum((p for curve,p in law.items() if curve[t]==j),
                             Fraction()) for j in range(len(c)+1))
        expected=distinct_count_pmf(c,t,sampler)
        assert calculated==expected
        mean=sum((curve[t]*p for curve,p in law.items()),Fraction())
        owner=(expected_iid_vocabulary(
            tuple(Fraction(x,n) for x in c),t)
            if sampler=="iid" else expected_permutation_vocabulary(c,t))
        assert mean==owner
    return law


def abc_joint_path_boundary() -> dict:
    """Classical six-order example: finite permutation curve deterministic."""
    c=(1,1,1)
    permutation=full_heaps_curve_law(c,3,"permutation")
    iid=full_heaps_curve_law(c,3,"iid")
    assert permutation=={(0,1,2,3):Fraction(1)}
    assert iid!=permutation
    assert iid.get((0,1,1,1),Fraction())>0
    return {"permutation":permutation,"iid":iid}


def aabc_joint_path_boundary() -> dict:
    """AABC: 12 source words / three Heaps curves under fixed permutation."""
    c=(2,1,1)
    permutation=full_heaps_curve_law(c,4,"permutation")
    iid=full_heaps_curve_law(c,4,"iid")
    assert permutation=={
      (0,1,1,2,3):Fraction(1,6),
      (0,1,2,2,3):Fraction(1,3),
      (0,1,2,3,3):Fraction(1,2),
    }
    assert iid!=permutation
    return {"permutation":permutation,"iid":iid}
