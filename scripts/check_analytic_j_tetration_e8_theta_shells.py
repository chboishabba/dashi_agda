#!/usr/bin/env python3
"""Exact integer regression: native E8 lattice theta shells versus 240*sigma_3.

E8 = {x in Z^8 : sum x_i even}
   union {x in (Z+1/2)^8 : sum x_i even}.
Represent doubled coordinates d_i=2*x_i. Thus:
  * all d_i even, or all d_i odd;
  * sum d_i divisible by 4;
  * sum d_i^2 = 8*n iff ||x||^2/2 = n.

This DP exhausts every integral/half-integral vector at each fixed norm
using integer arithmetic; it is NOT an analytic or Agda proof that the
identity holds for all n, nor a substitute for a theta modularity theorem.
"""

from math import isqrt


def e8_shell_count(index: int, parity: int) -> int:
    assert index >= 0 and parity in (0, 1)
    norm = 8 * index
    possible = tuple(
        d for d in range(-isqrt(norm), isqrt(norm) + 1)
        if d * d <= norm and d % 2 == parity
    )
    states = {(0, 0): 1}
    for _ in range(8):
        next_states = {}
        for (sum_squares, residue), multiplicity in states.items():
            for d in possible:
                new_norm = sum_squares + d * d
                if new_norm <= norm:
                    key = (new_norm, (residue + d) % 4)
                    next_states[key] = next_states.get(key, 0) + multiplicity
        states = next_states
    return states.get((norm, 0), 0)



def e8_unrestricted_and_projected(index: int, parity: int) -> tuple[int, int, int]:
    """Return (unrestricted shell, E8 parity-even shell, parity-odd shell).

    The exact mod-4 doubled-coordinate sum carries the native E8 lattice
    integrality condition. The signed theta_4 character on integral vectors
    is + on residue 0 and - on residue 2. For half vectors a sign reversal
    of one coordinate pairs residue 0 and residue 2, proving equal counts.
    """
    norm = 8 * index
    possible = tuple(
        d for d in range(-isqrt(norm), isqrt(norm) + 1)
        if d * d <= norm and d % 2 == parity
    )
    states = {(0, 0): 1}
    for _ in range(8):
        next_states = {}
        for (sum_squares, residue), multiplicity in states.items():
            for d in possible:
                new_norm = sum_squares + d * d
                if new_norm <= norm:
                    key = (new_norm, (residue + d) % 4)
                    next_states[key] = next_states.get(key, 0) + multiplicity
        states = next_states
    even = states.get((norm, 0), 0)
    odd = states.get((norm, 2), 0)
    return even + odd, even, odd


def check_theta_decomposition(index: int) -> None:
    """Check Theta_E8=(theta3^8+theta4^8+theta2^8)/2 coefficientwise.

    This function tests a finite coefficient. The all-index equality is
    justified combinatorially by the ±1 parity projector, and half-family
    parity cancellation under d_0 -> -d_0 (odd first coordinate). Its
    original Bishop analytic theta-series/winding formalization is OPEN.
    """
    theta3, integer_even, integer_odd = e8_unrestricted_and_projected(index, 0)
    theta2, half_even, half_odd = e8_unrestricted_and_projected(index, 1)
    theta4 = integer_even - integer_odd
    assert half_even == half_odd, (index, half_even, half_odd)
    assert 2 * integer_even == theta3 + theta4
    assert 2 * half_even == theta2
    assert 2 * (integer_even + half_even) == theta3 + theta4 + theta2

def sigma3(index: int) -> int:
    return sum(d ** 3 for d in range(1, index + 1) if index % d == 0)


def main() -> None:
    print("n integer-family half-family E8-shell Bishop-E4 PASS")
    for index in range(9):
        integral = e8_shell_count(index, 0)
        half = e8_shell_count(index, 1)
        actual = integral + half
        expected = 1 if index == 0 else 240 * sigma3(index)
        assert actual == expected, (index, integral, half, expected)
        check_theta_decomposition(index)
        print(index, integral, half, actual, expected, "PASS")
    print("PASS: exact E8 theta coefficients and theta2/theta3/theta4 parity split n=0..8 (finite regression only)")


if __name__ == "__main__":
    main()
