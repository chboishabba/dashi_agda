#!/usr/bin/env python3
"""Exact rational 8/27 selected Bishop chart finite-source control.

For p ∈ {27/20,3/2,2,5/2}, |t| in {0,1/200,1/50,1/10},
six exact rational unit-circle directions, and 30 successive original
shifted log terms, compute the true original partial-sum norm squared
against (8/27 * |t|^2)^2. No floating-point or assumed limit.

NOT an Agda proof, a Bishop-real sqrt construction, or a numerical
certificate for the original transcendental Newton fixed point.
"""
from fractions import Fraction as Q

PHASES = (
    (Q(1), Q(0)), (Q(0), Q(1)),
    (Q(3, 5), Q(4, 5)), (Q(5, 13), Q(12, 13)),
    (Q(-3, 5), Q(4, 5)), (Q(3, 5), Q(-4, 5)),
)
P = (Q(27, 20), Q(3, 2), Q(2), Q(5, 2))
T = (Q(0), Q(1, 200), Q(1, 50), Q(1, 10))


def multiply(a, b):
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def run():
    checked = 0
    assert Q(1, 2) * Q(20, 27)**2 * Q(27, 25) == Q(8, 27)
    for p in P:
        for t in T:
            for phase in PHASES:
                assert phase[0]**2 + phase[1]**2 == 1
                u = t * phase[0] / p, t * phase[1] / p
                assert u[0]**2 + u[1]**2 <= Q(2, 27)**2
                prefix = Q(0), Q(0)
                power = u
                for n in range(30):
                    power = multiply(power, u)
                    coefficient = Q((-1)**(n + 1), n + 2)
                    prefix = (
                        prefix[0] + coefficient * power[0],
                        prefix[1] + coefficient * power[1]
                    )
                    assert prefix[0]**2 + prefix[1]**2 <= (
                        Q(8, 27) * t * t
                    )**2
                    checked += 1
    assert checked == 2880
    print(f"PASS {checked}/{checked} exact selected original-log "
          "finite-sum 8/27 comparisons")
    print("BOUNDARY: source rational checks only; Agda 2.9 kernel, "
          "BishopSquareRootCalculus inhabitant and P1.N remain open")


if __name__ == "__main__":
    run()
