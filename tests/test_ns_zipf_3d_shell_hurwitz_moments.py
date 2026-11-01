"""Exact 3D Fourier-cube shell counts and Hurwitz moment identities.

This is a finite algebraic/spectral summability audit, NOT a Navier--Stokes
solution, and it does not assume that empirical magnitude ranks equal |k| ranks.
Sources: elementary lattice counting, classical zeta/Hurwitz and Fourier Sobolev
norm definitions; no new original attribution for those identities.
"""
from fractions import Fraction
from math import comb
import sympy as S


def shell_count(radius: int) -> int:
    if radius < 1:
        raise ValueError("positive shell radius required")
    return (2 * radius + 1) ** 3 - (2 * radius - 1) ** 3


def finite_shell_moment(n: int, beta: int, q: int, moment: int) -> Fraction:
    """Exact R-infinity shell sum; not the Euclidean norm value."""
    if n < 1 or q < 0 or beta < 0 or moment < 0:
        raise ValueError("requires n>=1, q,beta,moment>=0")
    return sum((Fraction(shell_count(r) * r ** moment, (r + q) ** beta)
                for r in range(1, n + 1)), Fraction())


def hurwitz_shell_moment(n: int, beta: int, q: int, moment: int):
    """Termwise binomial/Hurwitz finite difference in its convergent domain."""
    if n < 1 or q < 0 or moment < 0 or beta <= moment + 3:
        raise ValueError("require n>=1, q,moment>=0, beta>moment+3")

    def delta(t):
        return S.zeta(t, q + 1) - S.zeta(t, q + n + 1)

    return S.expand(
        24 * sum(comb(moment + 2, j) * (-q) ** (moment + 2 - j)
                 * delta(beta - j) for j in range(moment + 3))
        + 2 * sum(comb(moment, j) * (-q) ** (moment - j)
                  * delta(beta - j) for j in range(moment + 1))
    )


def test_original_three_dimensional_cube_shell_polynomial():
    r = S.symbols('r')
    assert S.expand((2 * r + 1) ** 3 - (2 * r - 1) ** 3 - 24 * r ** 2 - 2) == 0
    assert [shell_count(r) for r in range(1, 5)] == [26, 98, 218, 386]
    assert sum(shell_count(r) for r in range(1, 5)) == 9**3 - 1


def test_exact_shifted_hurwitz_identity_for_three_moments():
    for moment in (0, 1, 2):
        n, beta, q = 4, 7, 2
        lhs = finite_shell_moment(n, beta, q, moment)
        rhs = hurwitz_shell_moment(n, beta, q, moment)
        assert S.simplify(rhs - S.Rational(lhs.numerator, lhs.denominator)) == 0


def test_unshifted_zeta_normalizer_and_critical_moment_formula():
    # Summing k=(shell modes), the exact R-infinity critical moment is
    # 24 zeta(beta-3) + 2 zeta(beta-1) for beta > 4.
    assert S.simplify(hurwitz_shell_moment(4, 7, 0, 1) -
                      (24 * (S.zeta(4) - S.zeta(4, 5)) +
                       2 * (S.zeta(6) - S.zeta(6, 5)))) == 0


def test_endpoints_are_harmonic_and_do_not_summably_absorb():
    r = S.symbols('r', positive=True)
    for moment in (0, 1, 2):
        borderline_beta = moment + 3
        term = (24 * r**2 + 2) * r**moment / r**borderline_beta
        assert S.simplify(term - 24/r - 2/r**3) == 0
        # Positive 24/r tail forces divergence exactly at the endpoint.
        better = (24 * r**2 + 2) * r**moment / r**(borderline_beta + 1)
        assert S.simplify(better - 24/r**2 - 2/r**4) == 0


def test_sorted_frequency_rank_has_cube_growth_not_one_dimensional_density():
    for radius in range(1, 12):
        rank_through_shell = (2 * radius + 1)**3 - 1
        assert rank_through_shell == sum(shell_count(j) for j in range(1, radius + 1))
        assert rank_through_shell > 8 * radius**3
    # Physical per-mode decay beta induces rank exponent beta/3 ONLY
    # when ranking is actually by |k|_infinity (or compatible radial order).


def test_euclidean_fourier_weight_and_cube_weight_are_uniformly_equivalent():
    # For k != 0, R = ||k||infty <= ||k||2 <= sqrt(3) R.
    for x in range(-3, 4):
        for y in range(-3, 4):
            for z in range(-3, 4):
                r = max(abs(x), abs(y), abs(z))
                if r == 0:
                    continue
                length_squared = x*x + y*y + z*z
                assert r*r <= length_squared <= 3*r*r
