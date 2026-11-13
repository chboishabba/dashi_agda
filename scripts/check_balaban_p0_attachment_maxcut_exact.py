#!/usr/bin/env python3
"""Exact Fraction arithmetic audit for P0; no synthetic physical integrals.

This regression deliberately proves only rational identities, finite
tensor transversality/covariance, and source-indexed coefficient checks.
A PASS is NOT an Agda kernel receipt or a Wilson/ghost/Haar quadrature
certificate. The original physical source AST/analytic inputs remain open.
"""
from fractions import Fraction as F
from itertools import permutations, product


def p(k, i, j):
    return (sum(v*v for v in k) if i == j else F(0)) - k[i]*k[j]


def t(k, i, j):
    return sum(k[a]*k[a]*p(k, i, a)*p(k, a, j) for a in range(4))


def test_source_rationals():
    # Correct user's misstated rational square numerator.
    sine_floor = F(7071, 10000)
    assert 4*sine_floor*sine_floor == F(199996164, 100000000)
    assert 4*sine_floor*sine_floor > F(19999, 10000)
    assert 4*sine_floor*sine_floor < 2

    # SU(2) adjoint C_A = 2 and pure-gauge 11/3 coefficient.
    assert F(11, 3)*F(2)*F(1, 16) == F(11, 24)
    # SU2 exponential chart J=(sin(r/2)/(r/2))**2:
    haar_log_2 = -F(1, 12)
    haar_log_4 = -F(1, 1440)
    assert haar_log_2 == -F(1, 12)
    assert haar_log_4 + haar_log_2*haar_log_2/2 == F(1, 360)

    # Source 4^4 grid cells, 16 inner, 240 regular.
    weights = (64, 96, 64, 16)
    assert sum(weights) == 240
    assert [x//16 for x in weights] == [4, 6, 4, 1]
    h = F(1, 2)
    dx_vol = h**4
    physical_jacobian = F(1, 16)
    x_midpoint_factor = 4*h*h*dx_vol/F(24)
    physical_midpoint_factor = x_midpoint_factor*physical_jacobian
    assert x_midpoint_factor == F(1, 384)
    assert physical_midpoint_factor == F(1, 6144)
    assert sum(weights[i]*physical_midpoint_factor for i in range(4)) == F(15, 384)
    assert sum(weights[i]*dx_vol*physical_jacobian for i in range(4)) == F(15, 16)

    # Existing physical reduced ghost source R has row norm <= 1/5:
    # exact geometric majorant for all signed/unsigned n>=5 terms.
    assert F(1, 5)**5 / (1 - F(1, 5)) == F(1, 2500)
    # Shifted denominator rational check is only a scalar consequence;
    # source vector Lipschitz and same-Fourier atom identification OPEN.
    root_lower = F(14141, 10000)
    shift_upper = F(3927, 10000)
    assert root_lower*root_lower < F(19999, 10000)
    assert (root_lower - shift_upper)**2 > F(1043, 1000)


def test_tensor_transversality_and_covariance():
    # P(k) = k^2 I - k k^T.
    # T(k) = P(k) diag(k_i^2) P(k) is an even, B4-covariant
    # transverse polynomial tensor, generally NOT scalar * P(k).
    k = tuple(map(F, (1, 2, 3, 4)))
    assert all(sum(k[i]*t(k, i, j) for i in range(4)) == 0
               for j in range(4))
    seen = 0
    for perm in permutations(range(4)):
        for signs in product((-1, 1), repeat=4):
            k2 = tuple(signs[i]*k[perm[i]] for i in range(4))
            for i in range(4):
                for j in range(4):
                    assert p(k2, i, j) == signs[i]*signs[j]*p(k, perm[i], perm[j])
                    assert t(k2, i, j) == signs[i]*signs[j]*t(k, perm[i], perm[j])
            seen += 1
    assert seen == 384

    k = tuple(map(F, (1, 2, 0, 0)))
    assert all(sum(k[i]*t(k, i, j) for i in range(4)) == 0
               for j in range(4))
    assert p(k, 0, 0) == 4 and p(k, 2, 2) == 5
    assert t(k, 0, 0) == 32 and t(k, 2, 2) == 0
    # Necessary cross-multiplication equality for T(k)=c P(k) fails.
    assert t(k, 0, 0)*p(k, 2, 2) == 160
    assert t(k, 2, 2)*p(k, 0, 0) == 0


if __name__ == "__main__":
    test_source_rationals()
    test_tensor_transversality_and_covariance()
    print("PASS exact rational sine, SU2 color/Haar, ghost tail,")
    print("     4D Brillouin measure and midpoint/Hessian coefficients.")
    print("PASS exact Ward transversality and 384 simultaneous B4")
    print("     signed-permutation tests for nonfactorizing tensor T.")
    print("OPEN physical diagram numerators, source Ward/phase covariance,")
    print("     Fourier sine and shifted denominators, 4 beta integrals,")
    print("     true Hessian/errors, P0.12 coefficient/remainder and Agda kernel.")
