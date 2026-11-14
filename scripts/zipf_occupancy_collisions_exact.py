"""Exact rational finite occupancy and concentration under typed sampling schemes.

Mathematical lineage: classical occupancy/inclusion-exclusion; Simpson's
diversity / Herfindahl-Hirschman concentration. New repository synthesis
and regression: Johl Brown with OpenAI ChatGPT assistance, 2026-10-27.
No empirical universal law follows from a finite occupancy identity.
"""
from __future__ import annotations
from fractions import Fraction
from itertools import combinations
from math import comb
from typing import Sequence
from zipf_heaps_bridge import (
    _validated_pmf, _validated_counts,
    expected_iid_vocabulary, expected_permutation_vocabulary,
)

def iid_collision_probability(masses: Sequence[Fraction]) -> Fraction:
    """Pr(X1=X2)=sum p_i²; explicitly IID draws with replacement."""
    p=_validated_pmf(masses)
    return sum((x*x for x in p),Fraction())

def iid_two_draw_vocabulary(masses: Sequence[Fraction]) -> Fraction:
    return 2-iid_collision_probability(masses)

def iid_three_draw_vocabulary(masses: Sequence[Fraction]) -> Fraction:
    p=_validated_pmf(masses)
    return 3-3*sum((x*x for x in p),Fraction())+sum((x**3 for x in p),Fraction())

def iid_novelty_second_difference(masses: Sequence[Fraction], prior_draws: int) -> Fraction:
    """E[V(t+2)]-2E[V(t+1)]+E[V(t)]= -sum p_i²(1-p_i)^t."""
    p=_validated_pmf(masses)
    if not isinstance(prior_draws,int) or prior_draws<0:raise ValueError('t>=0 integer')
    return -sum((x*x*(1-x)**prior_draws for x in p),Fraction())

def iid_vocabulary_variance(masses: Sequence[Fraction], draws: int) -> Fraction:
    """Exact variance via presence-indicator covariances."""
    p=_validated_pmf(masses)
    if not isinstance(draws,int) or draws<0:raise ValueError('draws>=0 integer')
    miss=[(1-x)**draws for x in p]
    diagonal=sum((a*(1-a) for a in miss),Fraction())
    cross=sum(((1-p[i]-p[j])**draws-miss[i]*miss[j]
               for i,j in combinations(range(len(p)),2)),Fraction())
    result=diagonal+2*cross
    assert result>=0
    return result

def iid_variance_upper_bound(masses:Sequence[Fraction],draws:int)->Fraction:
    """Negative indicator covariances imply Var(V_n)<=E[V_n]."""
    p=_validated_pmf(masses)
    variance=iid_vocabulary_variance(p,draws)
    mean=expected_iid_vocabulary(p,draws)
    assert variance<=mean
    return mean

def permutation_collision_probability(counts:Sequence[int])->Fraction:
    """Pr(same type in first 2 of uniformly permuted fixed multiset)."""
    c=_validated_counts(counts);n=sum(c)
    if n<2:raise ValueError('at least two tokens')
    return Fraction(sum(f*(f-1) for f in c),n*(n-1))

def permutation_two_draw_vocabulary(counts:Sequence[int])->Fraction:
    return 2-permutation_collision_probability(counts)

def permutation_vocabulary_variance(counts:Sequence[int],draws:int)->Fraction:
    """Exact variance from hypergeometric pairwise indicator inclusion/exclusion."""
    c=_validated_counts(counts);n=sum(c)
    if not isinstance(draws,int) or not 0<=draws<=n:raise ValueError('draws in corpus')
    den=comb(n,draws)
    miss=[Fraction(comb(n-f,draws),den) for f in c]
    diagonal=sum((m*(1-m) for m in miss),Fraction())
    cross=sum((Fraction(comb(n-c[i]-c[j],draws),den)-miss[i]*miss[j]
               for i,j in combinations(range(len(c)),2)),Fraction())
    result=diagonal+2*cross
    assert result>=0
    return result

def iid_effective_type_count(masses:Sequence[Fraction])->Fraction:
    """Inverse Simpson probability of coincidence (Hill order-two)."""
    return 1/iid_collision_probability(masses)

def exact_uniform_collision_bound(masses:Sequence[Fraction])->tuple[Fraction,Fraction]:
    """1/K <= sum p_i² <= 1; left equality at uniform distribution."""
    p=_validated_pmf(masses)
    result=iid_collision_probability(p)
    assert Fraction(1,len(p))<=result<=1
    return Fraction(1,len(p)),Fraction(1)

def two_draw_without_vs_with_replacement_gap(counts:Sequence[int])->Fraction:
    """E[V2]_without-E[V2]_IID = (N²-sum f_i²)/(N²(N-1))."""
    c=_validated_counts(counts);n=sum(c)
    if n<2:raise ValueError('at least two tokens')
    p=tuple(Fraction(f,n) for f in c)
    result=permutation_two_draw_vocabulary(c)-iid_two_draw_vocabulary(p)
    assert result==Fraction(n*n-sum(f*f for f in c),n*n*(n-1))
    assert result>=0
    return result
