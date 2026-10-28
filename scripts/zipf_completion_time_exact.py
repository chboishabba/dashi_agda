"""Exact time until every type is first observed, for two finite samplers.

Reuse the canonical Heaps count validator and majorization relation. The
IID collector can continue past N draws; a fixed-multiset permutation cannot.
Exact inclusion-exclusion is exponential in the number of types. Formulae
are classical coupon-collector occupancy identities (not a new discovery).
Historical root: de Moivre; modern majorization framework HLP (1934),
Marshall/Olkin/Arnold (2011). Repository adapter: Johl Brown with OpenAI
ChatGPT assistance (2026-10-28). No Agda-kernel or empirical claim.
"""
from __future__ import annotations

from fractions import Fraction
from math import comb
from typing import Literal, Sequence

from zipf_heaps_bridge import _validated_counts, multiset_count_majorizes

Sampler = Literal['iid', 'permutation']


def _inputs(counts: Sequence[int], sampler: Sampler) -> tuple[tuple[int, ...], int]:
    c = _validated_counts(counts)
    if sampler not in ('iid', 'permutation'):
        raise ValueError('sampler must be iid or permutation')
    # Exact subset enumeration is exponential. Refuse implicit huge allocations.
    if len(c) > 18:
        raise ValueError('exact subset evaluator limited to <=18 types')
    return c, sum(c)


def _nonempty_subsets(counts: tuple[int, ...]):
    """Yield (subset token sum, inclusion-exclusion sign) for nonempty sets."""
    for mask in range(1, 1 << len(counts)):
        token_sum = sum(counts[i] for i in range(len(counts)) if mask & (1 << i))
        sign = 1 if mask.bit_count() & 1 else -1
        yield token_sum, sign


def completion_cdf(counts: Sequence[int], draws: int, sampler: Sampler) -> Fraction:
    """Exact P(all K types seen by t). IID t>=0; permutation 0<=t<=N.

    Inclusion-exclusion: 1 - sum_{A nonempty} (-1)^{|A|+1}
    P(no type in A in first t draws). This is not an empirical Zipf law.
    """
    c, n = _inputs(counts, sampler)
    if type(draws) is not int or draws < 0 or (sampler == 'permutation' and draws > n):
        raise ValueError('valid nonnegative draw count, at most N for permutation')
    total = Fraction(1)
    for subset_count, sign in _nonempty_subsets(c):
        missing = (Fraction(n - subset_count, n) ** draws if sampler == 'iid'
                   else Fraction(comb(n - subset_count, draws), comb(n, draws)))
        total -= sign * missing
    assert 0 <= total <= 1
    return total


def completion_mean(counts: Sequence[int], sampler: Sampler) -> Fraction:
    """Exact E[T], where T is first draw count with ALL types observed.

    IID: N * sum_{A != empty} (-1)^{|A|+1} / sum_{i in A} f_i.
    Permutation: (N+1)*sum_{A != empty} (-1)^{|A|+1}/(1+sum_A f_i).
    The latter follows from the hockey-stick sum of hypergeometric tails.
    """
    c, n = _inputs(counts, sampler)
    result = sum((Fraction(sign, subtotal if sampler == 'iid' else subtotal+1)
                  for subtotal, sign in _nonempty_subsets(c)), Fraction())
    result *= n if sampler == 'iid' else n + 1
    assert 1 <= result and (sampler == 'iid' or result <= n)
    return result


def completion_tail_bounds(counts: Sequence[int], draws: int, sampler: Sampler
                           ) -> tuple[Fraction, Fraction, Fraction]:
    """Exact missing-type tail between max-singleton and union-bound values.

    Returns lower, actual, upper. No equality is implied unless verified.
    """
    c, n = _inputs(counts, sampler)
    if type(draws) is not int or draws < 0 or (sampler == 'permutation' and draws > n):
        raise ValueError('invalid draw horizon for sampler')
    absent = tuple(Fraction(n - f, n) ** draws if sampler == 'iid' else
                   Fraction(comb(n - f, draws), comb(n, draws)) for f in c)
    lower = max(absent)
    upper = min(Fraction(1), sum(absent, Fraction()))
    actual = 1 - completion_cdf(c, draws, sampler)
    assert lower <= actual <= upper
    return lower, actual, upper


def majorization_completion_certificate(concentrated: Sequence[int],
                                         dispersed: Sequence[int],
                                         iid_horizon: int
                                         ) -> dict[str, tuple[Fraction, Fraction, Fraction, Fraction]]:
    """Completion-CDF and expected-time order for concentrated >= dispersed.

    Returns (cdf_concentrated, cdf_dispersed, E_T_concentrated,
    E_T_dispersed) per sampler. Permutation CDF is capped at t<=N,
    while the IID CDF may be checked beyond N. A distributional consequence
    of canonical finite occupancy majorization, NOT an empirical result.
    """
    if not multiset_count_majorizes(concentrated, dispersed):
        raise ValueError('same K,N and concentrated majorizes dispersed required')
    c, n = _inputs(concentrated, 'iid')
    _inputs(dispersed, 'iid')
    if type(iid_horizon) is not int or iid_horizon < 0:
        raise ValueError('IID horizon must be a nonnegative integer')
    out = {}
    for sampler in ('iid', 'permutation'):
        horizon = iid_horizon if sampler == 'iid' else min(n, iid_horizon)
        cdf_c = completion_cdf(c, horizon, sampler)
        cdf_d = completion_cdf(dispersed, horizon, sampler)
        mean_c = completion_mean(c, sampler)
        mean_d = completion_mean(dispersed, sampler)
        assert cdf_c <= cdf_d and mean_c >= mean_d
        out[sampler] = (cdf_c, cdf_d, mean_c, mean_d)
    return out
