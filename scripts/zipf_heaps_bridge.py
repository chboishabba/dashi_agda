"""Exact finite Zipf/Heaps occupancy bridges with explicit sampling assumptions.

The Heaps expectation is *conditional* on IID draws, not a deterministic
consequence of a histogram; uniform permutations of a fixed multiset are a
separate model. Historical/provenance references belong to the research note.
"""
from __future__ import annotations
from fractions import Fraction
from math import comb
from typing import Sequence


def finite_rank_probabilities(n: int, exponent: int, shift: int = 0) -> tuple[Fraction, ...]:
    """Exact shifted Zipf PMF for nonnegative *integer* shape parameters."""
    if not isinstance(n, int) or isinstance(n, bool) or n < 1:
        raise ValueError('positive finite support')
    if any(not isinstance(v, int) or isinstance(v, bool) or v < 0
           for v in (exponent, shift)):
        raise ValueError('nonnegative integer exponent and shift')
    terms = tuple(Fraction(1, (r + shift) ** exponent) for r in range(1, n + 1))
    z = sum(terms, Fraction())
    return tuple(t / z for t in terms)


def finite_cdf(masses: Sequence[Fraction]) -> tuple[Fraction, ...]:
    p = _validated_pmf(masses)
    cumulative = Fraction()
    out = []
    for value in p:
        cumulative += value
        out.append(cumulative)
    return tuple(out)


def finite_quantile(masses: Sequence[Fraction], threshold: Fraction) -> int:
    """Least 1-based rank with cumulative mass >= threshold, threshold (0,1]."""
    if not isinstance(threshold, Fraction) or not Fraction() < threshold <= 1:
        raise ValueError('threshold must be Fraction in (0,1]')
    for rank, mass in enumerate(finite_cdf(masses), 1):
        if mass >= threshold:
            return rank
    raise AssertionError('normalized finite mass must cross threshold')


def finite_rank_moment(masses: Sequence[Fraction], order: int) -> Fraction:
    p = _validated_pmf(masses)
    if not isinstance(order, int) or order < 0:
        raise ValueError('nonnegative moment order')
    return sum((mass * rank ** order for rank, mass in enumerate(p, 1)), Fraction())


def _validated_pmf(masses: Sequence[Fraction]) -> tuple[Fraction, ...]:
    p = tuple(masses)
    if not p or any(not isinstance(x, Fraction) or x < 0 for x in p) or sum(p) != 1:
        raise ValueError('nonempty normalized rational PMF')
    return p


def expected_iid_vocabulary(masses: Sequence[Fraction], draws: int) -> Fraction:
    """E[V_draws] = sum_i(1-(1-p_i)^draws), given IID sampling."""
    p = _validated_pmf(masses)
    if not isinstance(draws, int) or draws < 0:
        raise ValueError('draws must be nonnegative integer')
    return sum((1 - (1 - mass) ** draws for mass in p), Fraction())


def expected_iid_new_type(masses: Sequence[Fraction], prior_draws: int) -> Fraction:
    """Exact discrete derivative E[V_(n+1)]-E[V_n]."""
    p = _validated_pmf(masses)
    if not isinstance(prior_draws, int) or prior_draws < 0:
        raise ValueError('prior_draws must be nonnegative integer')
    return sum((mass * (1 - mass) ** prior_draws for mass in p), Fraction())


def expected_permutation_vocabulary(counts: Sequence[int], draws: int) -> Fraction:
    """E[V_draws] when uniformly permuting an actual finite multiset.

    Distinct from replacement-IID even with identical limiting proportions.
    """
    c = _validated_counts(counts)
    total = sum(c)
    if not isinstance(draws, int) or not 0 <= draws <= total:
        raise ValueError('draws must be in [0,total tokens]')
    denominator = comb(total, draws)
    return sum((1 - Fraction(comb(total - f, draws), denominator)
                for f in c), Fraction())


def distinct_envelope(counts: Sequence[int], draws: int) -> tuple[int, int]:
    """Tight minimum/maximum type counts over ALL permutations of multiset."""
    c = _validated_counts(counts)
    total = sum(c)
    if not isinstance(draws, int) or not 0 <= draws <= total:
        raise ValueError('draws must be in [0,total tokens]')
    if draws == 0:
        return (0, 0)
    filled = 0
    lower = 0
    for f in sorted(c, reverse=True):
        filled += f
        lower += 1
        if filled >= draws:
            break
    return lower, min(draws, len(c))


def _validated_counts(counts: Sequence[int]) -> tuple[int, ...]:
    c = tuple(counts)
    if not c or any(not isinstance(f, int) or isinstance(f, bool) or f < 1 for f in c):
        raise ValueError('nonempty strictly positive token-type counts')
    return c


def dyadic_block_entropy(probs: Sequence[Fraction]) -> Fraction:
    """Exact Shannon bits on a finite distribution whose atoms are 2^-k.

    Only this dyadic subclass; not a general entropy solver and not Hilberg.
    """
    p = _validated_pmf(probs)
    entropy = Fraction()
    for mass in p:
        if mass == 0:
            continue
        if mass.numerator != 1 or mass.denominator & (mass.denominator - 1):
            raise ValueError('this certificate needs dyadic atom masses 2^-k')
        entropy += mass * (mass.denominator.bit_length() - 1)
    return entropy


def finite_hurwitz_sum(n: int, exponent: int, shift: int = 0) -> Fraction:
    """Exact *finite* H_N(shift,exponent), including nonpositive exponents."""
    if not isinstance(n,int) or n<0 or not isinstance(exponent,int) or not isinstance(shift,int) or shift<0:
        raise ValueError('n,shift nonnegative integers; exponent integer')
    return sum((Fraction(r + shift, 1) ** (-exponent) for r in range(1, n+1)), Fraction())


def finite_shifted_moment_binomial(n: int, exponent: int, shift: int, order: int) -> Fraction:
    """Exact E[R^m] via H_N(shift,s-j) and the binomial theorem."""
    if not isinstance(order,int) or order<0:
        raise ValueError('nonnegative moment order')
    z = finite_hurwitz_sum(n,exponent,shift)
    if z<=0:
        raise ValueError('positive finite support required')
    numerator = sum((comb(order,j) * (-shift)**(order-j) * finite_hurwitz_sum(n,exponent-j,shift)
                    for j in range(order+1)), Fraction())
    return numerator/z


def conditioned_head(masses: Sequence[Fraction], keep: int) -> tuple[Fraction, ...]:
    """Finite Zipf law conditioned on ranks <= keep, zeros elsewhere."""
    p = _validated_pmf(masses)
    if not isinstance(keep,int) or not 1 <= keep <= len(p):
        raise ValueError('head cutoff in [1,support length]')
    headmass = sum(p[:keep],Fraction())
    if headmass == 0:
        raise ValueError('cannot condition on a zero probability event')
    return tuple(m/headmass for m in p[:keep]) + (Fraction(),)*(len(p)-keep)


def l1_probability_distance(a:Sequence[Fraction],b:Sequence[Fraction])->Fraction:
    """L1 of two finite PMFs; mathlib's variation norm, not sup_A TV."""
    p=_validated_pmf(a); q=_validated_pmf(b)
    if len(p)!=len(q):
        raise ValueError('same common support required')
    return sum((abs(x-y) for x,y in zip(p,q)),Fraction())


def novelty_flags(tokens:Sequence[str])->tuple[bool,...]:
    """Indicates whether each token is a new type, retaining chronological order."""
    seen=set();out=[]
    for token in tokens:
        new=token not in seen
        out.append(new)
        seen.add(token)
    return tuple(out)


def equal_flag_runs(flags:Sequence[bool])->tuple[tuple[bool,int],...]:
    """Run lengths preserve information lost by rank counts and final Heaps."""
    result=[]
    for b in flags:
        if result and result[-1][0]==b:
            result[-1]=(b,result[-1][1]+1)
        else:
            result.append((b,1))
    return tuple(result)


def extremal_multiset_token_orders(counts: Sequence[int]) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """Two constructive chronological orders realizing the WHOLE tight envelope.

    The first fills types by descending declared count and minimizes observed
    prefix diversity at every prefix length simultaneously. The second visits
    each type once before any repeated token, maximizing it at every prefix.
    A fixed type index resolves tied counts; no empirical chronology is inferred.
    Original extremal discovery-process context: Zimmerlin et al., PRE 2026.
    """
    c = _validated_counts(counts)
    ranked = sorted(enumerate(c), key=lambda pair: (-pair[1], pair[0]))
    lower_order = tuple(i for i, n in ranked for _ in range(n))
    upper_order = tuple(i for i, _ in ranked) + tuple(
        i for i, n in ranked for _ in range(n - 1)
    )
    return lower_order, upper_order


def observed_prefix_diversity(tokens: Sequence[int]) -> tuple[int, ...]:
    """Prefix type count, INCLUDING the empty prefix at t=0."""
    seen = set()
    curve = [0]
    for token in tokens:
        seen.add(token)
        curve.append(len(seen))
    return tuple(curve)


def multiset_heaps_extremal_profiles(counts: Sequence[int]) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """Sharp bounds for every t=0..N with exact attainable witness orders."""
    c = _validated_counts(counts)
    low, high = extremal_multiset_token_orders(c)
    lower = observed_prefix_diversity(low)
    upper = observed_prefix_diversity(high)
    # Independent per-t prefix-budget certificate already in this module.
    assert all((lower[t], upper[t]) == distinct_envelope(c, t)
               for t in range(sum(c) + 1))
    return lower, upper


def multiset_heaps_area_gap(counts: Sequence[int]) -> int:
    """Exact MAX-minus-MIN area under the all-prefix diversity curve.

    If sorted counts f_1>=...>=f_K>0 and S_j=sum_(i<=j) f_i,
    gap=sum_(j=0)^(K-1) S_j - K(K-1)/2, independent of word labels.
    This measures information about temporal order NOT retained by ranks.
    """
    c = sorted(_validated_counts(counts), reverse=True)
    prefix = 0
    lower_birthsum = 0
    for count in c:
        lower_birthsum += prefix
        prefix += count
    gap = lower_birthsum - len(c) * (len(c) - 1) // 2
    assert gap >= 0
    return gap
