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
        print(index, integral, half, actual, expected, "PASS")
    print("PASS: exact E8 theta coefficients n=0..8 (finite regression only)")


if __name__ == "__main__":
    main()
