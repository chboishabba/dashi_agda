"""Finite Zipf/Hurwitz audit and phase-blind obstruction on the ORIGINAL R734 source.

No statistical rank law is a Navier--Stokes regularity or signed-transfer theorem.
Historical credit: Zipf/Estoup, Mandelbrot, Hurwitz, Waleffe (1992),
Clauset--Shalizi--Newman (2009); the physical witness belongs to R734 PR #1271.
This test adds finite-rank comparisons, not a new independent fluid witness.
"""
from fractions import Fraction
import sympy as S
from test_ns_r734_pure_plus_physical_w2_no_go import (
    K, P, Q, minus, physical_u, projected_NS_nonlinearity,
    critical_data, weight,
)


def finite_zipf_normalizer(n: int, s: int, q: int = 0) -> Fraction:
    """Exact truncated sum; only the nonnegative integer q,s audit subdomain."""
    if n < 1 or s < 0 or q < 0:
        raise ValueError("requires n>=1, s>=0, q>=0")
    return sum((Fraction(1, (k + q) ** s) for k in range(1, n + 1)), Fraction())


def top_mass(n: int, k: int, s: int, q: int = 0) -> Fraction:
    if not (0 <= k <= n):
        raise ValueError("top-k count must be in [0,n]")
    if k == 0:
        return Fraction(0)
    return finite_zipf_normalizer(k, s, q) / finite_zipf_normalizer(n, s, q)


def modal_magnitudes(u):
    """Exact squared Fourier modal magnitudes, preserving physical mode identity."""
    return {m: S.simplify(S.expand_complex((S.conjugate(v).T * v)[0]))
            for m, v in u.items()}


def nonlinear_weighted_work(u):
    force = projected_NS_nonlinearity(u, 2)
    return S.simplify(S.expand_complex(sum((
        2 * weight(m) * S.re((S.conjugate(v).T * force.get(m, S.zeros(3, 1)))[0])
        for m, v in u.items()), S.Integer(0))))


def test_finite_hurwitz_zeta_difference_is_exact():
    n, s, q = 4, 2, 2
    finite = finite_zipf_normalizer(n, s, q)
    difference = S.zeta(s, q + 1) - S.zeta(s, n + q + 1)
    assert S.simplify(difference - S.Rational(finite.numerator, finite.denominator)) == 0
    assert top_mass(n, n, s, q) == 1
    assert top_mass(n, 0, s, q) == 0
    assert top_mass(n, 1, s, q) < top_mass(n, 2, s, q) < 1


def test_zipf_pareto_is_not_universal_eighty_twenty():
    assert top_mass(5, 1, 0) == Fraction(1, 5)  # uniform
    assert top_mass(5, 1, 1) == Fraction(60, 137)  # harmonic rank law
    assert top_mass(5, 1, 4) > Fraction(4, 5)  # steep tail
    # No rank-only theorem says "1% of raw factors" = "99% of gaps".


def test_exact_same_modal_ranks_have_opposite_r734_transfer():
    u = physical_u()
    v = {m: -a if m in (K, minus(K)) else a for m, a in u.items()}
    mag_u, mag_v = modal_magnitudes(u), modal_magnitudes(v)
    assert mag_u == mag_v
    assert S.simplify(sum(mag_u.values()) - sum(mag_v.values())) == 0
    positive = nonlinear_weighted_work(u)
    negative = nonlinear_weighted_work(v)
    assert S.simplify(positive - critical_data()[2]) == 0
    assert S.simplify(positive + negative) == 0
    assert S.simplify(positive > 0) == S.true
    # Every rank/magnitude-only statistic (not merely one fitted law)
    # is identical; the signed nonlinear work changes sign.


def test_full_sign_reversal_retains_pressure_but_flips_weighted_work():
    u = physical_u()
    reverse = {m: -v for m, v in u.items()}
    assert modal_magnitudes(u) == modal_magnitudes(reverse)
    f, fr = projected_NS_nonlinearity(u, 2), projected_NS_nonlinearity(reverse, 2)
    assert set(f) == set(fr)
    assert all(S.simplify(f[m] - fr[m]) == S.zeros(3, 1) for m in f)
    assert S.simplify(nonlinear_weighted_work(u) + nonlinear_weighted_work(reverse)) == 0
    # -Delta p = partial_i partial_j(u_i u_j), so p[-u] = p[u]
    # after the zero-mean gauge fix. Pressure parity does not imply
    # equality of its cubic velocity-weighted energy transfer.


def test_amplitude_normalized_ranks_cannot_bound_cubic_transfer():
    u = physical_u()
    a = S.Integer(512)
    amplified = {m: a * v for m, v in u.items()}
    mags = modal_magnitudes(u)
    mags_a = modal_magnitudes(amplified)
    total = sum(mags.values())
    total_a = sum(mags_a.values())
    assert total > 0
    for m in u:
        assert S.simplify(mags_a[m] / total_a - mags[m] / total) == 0
    assert S.simplify(nonlinear_weighted_work(amplified) - a**3 * critical_data()[2]) == 0
    # Literal R734 dissipation is quadratic, whereas production is cubic.
    _, dissipation, production = critical_data()
    assert S.simplify(a * production - 2 * dissipation > 0) == S.true
