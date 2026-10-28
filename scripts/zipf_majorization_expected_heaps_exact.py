"""Schur-concave expected vocabulary under TWO explicitly distinct samplers.

Reusable owners: finite_rank_probabilities, expected_iid_vocabulary,
expected_permutation_vocabulary, multiset_count_majorizes. No duplicate
probability carrier; all calculations in exact fractions.

Original mathematical result: classical majorization/concavity of finite
occupancy expectation; Hardy, Littlewood and Polya, Inequalities (1934).
Independent temporal-dependence context: Zimmerlin et al., PRE 2026.
Repository synthesis: Johl Brown with OpenAI ChatGPT assistance, 2026-10-28.
No universal Zipf/Heaps or physical same-object conclusion is asserted.
"""
from __future__ import annotations
from fractions import Fraction
from math import comb
from typing import Sequence
from zipf_heaps_bridge import (
    _validated_counts,
    expected_iid_vocabulary,
    expected_permutation_vocabulary,
    finite_rank_probabilities,
    multiset_count_majorizes,
)


def transfer_one_token_to_larger_type(
    counts: Sequence[int], richer: int, poorer: int
) -> tuple[int, ...]:
    """Move one token from a smaller type to a larger type, keep both positive."""
    c = list(_validated_counts(counts))
    if (type(richer) is not int or type(poorer) is not int or richer == poorer
            or not 0 <= richer < len(c) or not 0 <= poorer < len(c)
            or c[richer] < c[poorer] or c[poorer] < 2):
        raise ValueError('distinct valid indices, source >=2, destination >= source')
    c[richer] += 1
    c[poorer] -= 1
    return tuple(c)


def _count_pmf(counts: Sequence[int]) -> tuple[Fraction, ...]:
    c = _validated_counts(counts)
    total = sum(c)
    return tuple(Fraction(x, total) for x in c)


def _two_sampler_means(counts: Sequence[int], draws: int) -> tuple[Fraction, Fraction]:
    c = _validated_counts(counts)
    if type(draws) is not int or not 0 <= draws <= sum(c):
        raise ValueError('0<=draws<=total; both samplers compared on same window')
    return (expected_iid_vocabulary(_count_pmf(c), draws),
            expected_permutation_vocabulary(c, draws))


def majorization_expected_vocabulary_certificate(
    concentrated: Sequence[int], dispersed: Sequence[int], draws: int
) -> tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]:
    """Means (concentrated, dispersed) for IID and permutation samplers.

    Majorization f >= g and equal fixed K,N imply E_f[V_t] <= E_g[V_t]
    for each sampler. This is a conditional finite Schur-concavity theorem.
    Return values are executable certificate checks, NOT Agda-kernel proofs.
    """
    if not multiset_count_majorizes(concentrated, dispersed):
        raise ValueError('majorization prerequisite not established')
    fi, fp = _two_sampler_means(concentrated, draws)
    gi, gp = _two_sampler_means(dispersed, draws)
    assert fi <= gi, 'IID Schur-concavity violated'
    assert fp <= gp, 'permutation Schur-concavity violated'
    return (fi, gi), (fp, gp)


def one_transfer_expected_loss(
    counts: Sequence[int], richer: int, poorer: int, draws: int
) -> tuple[Fraction, Fraction]:
    """Old minus new vocabulary means after one concentrating count transfer."""
    c = _validated_counts(counts)
    concentrated = transfer_one_token_to_larger_type(c, richer, poorer)
    (new_i, old_i), (new_p, old_p) = majorization_expected_vocabulary_certificate(
        concentrated, c, draws)
    return old_i - new_i, old_p - new_p


def local_one_step_presence_gain(
    total: int, count: int, draws: int
) -> tuple[Fraction, Fraction]:
    """Discrete marginal gains in E[V] at occupancy count k.

    IID: ((N-k)/N)^n - ((N-k-1)/N)^n.
    Permutation: C(N-k-1,t-1)/C(N,t) for t>=1, and 0 if t=0.
    Both are nonincreasing as k increases; this proves the transfer step.
    """
    if (type(total) is not int or total < 1 or type(count) is not int
            or not 0 <= count < total or type(draws) is not int
            or not 0 <= draws <= total):
        raise ValueError('N>=1, 0<=count<N, 0<=draws<=N')
    iid = (Fraction(total-count, total) ** draws
           - Fraction(total-count-1, total) ** draws)
    permutation = (Fraction(comb(total-count-1, draws-1), comb(total, draws))
                   if draws else Fraction())
    return iid, permutation


def zipf_shape_majorization_certificate(
    support: int, smaller_exponent: int, larger_exponent: int, shift: int = 0
) -> tuple[tuple[Fraction, ...], tuple[Fraction, ...]]:
    """Increasing nonnegative integer Zipf exponent increases rank concentration.

    Finite-rank model with fixed support and shift. The likelihood ratio
    (r+q)^(-(larger-smaller)) is nonincreasing in rank. Therefore the
    high-exponent normalized vector majorizes the low-exponent vector.
    Returned vectors preserve sorted 1-based ranks, not re-fit data.
    """
    if (type(smaller_exponent) is not int or type(larger_exponent) is not int
            or smaller_exponent < 0 or larger_exponent < smaller_exponent):
        raise ValueError('0<=smaller exponent<=larger exponent')
    low = finite_rank_probabilities(support, smaller_exponent, shift)
    high = finite_rank_probabilities(support, larger_exponent, shift)
    run_high = run_low = Fraction()
    for h, l in zip(high, low):
        run_high += h
        run_low += l
        assert run_high >= run_low
    assert run_high == run_low == 1
    return low, high


def zipf_exponent_iid_heaps_certificate(
    support: int, smaller_exponent: int, larger_exponent: int,
    shift: int, draws: int
) -> tuple[Fraction, Fraction]:
    """Expected IID diversity under (larger exponent, smaller exponent)."""
    low, high = zipf_shape_majorization_certificate(
        support, smaller_exponent, larger_exponent, shift)
    if type(draws) is not int or draws < 0:
        raise ValueError('draws must be a nonnegative integer')
    low_v = expected_iid_vocabulary(low, draws)
    high_v = expected_iid_vocabulary(high, draws)
    assert high_v <= low_v
    return high_v, low_v
