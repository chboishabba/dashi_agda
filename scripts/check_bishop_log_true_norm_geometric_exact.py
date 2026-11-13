#!/usr/bin/env python3
"""Exact-rational negative/positive control for original Bishop P1.L finite logic.

Tests literal shifted logarithm term, Euclidean complex norm-square,
and sharp finite geometric bound for rational complex points on six
unit-circle phases. The Agda source proof has a separate constructive
Bishop real setoid and still requires pinned Agda 2.9 kernel acceptance,
the underlying BishopSquareRootCalculus inhabitant, and source limit
interpretation. This script is deliberately NOT an Agda certificate.
"""
from fractions import Fraction as Q


def multiply(left, right):
    return (
        left[0] * right[0] - left[1] * right[1],
        left[0] * right[1] + left[1] * right[0],
    )


def norm_square(value):
    return value[0] ** 2 + value[1] ** 2


def check():
    radii = [Q(i, 500) for i in range(36)] + [Q(2, 27)]
    phases = [
        (Q(1), Q(0)),
        (Q(0), Q(1)),
        (Q(3, 5), Q(4, 5)),
        (Q(5, 13), Q(12, 13)),
        (Q(-3, 5), Q(4, 5)),
        (Q(3, 5), Q(-4, 5)),
    ]
    total = 0
    for radius in radii:
        for phase in phases:
            w = radius * phase[0], radius * phase[1]
            power = w
            prefix = Q(0), Q(0)
            majorant = Q(0)
            for n in range(17):
                # a_(n+1)(w) = (-1)^(n+1) w^(n+2)/(n+2).
                coefficient = Q((-1) ** (n + 1), n + 2)
                power = multiply(power, w)
                term = coefficient * power[0], coefficient * power[1]
                assert norm_square(term) == (
                    coefficient**2 * radius ** (2 * (n + 2))
                )
                prefix = prefix[0] + term[0], prefix[1] + term[1]
                majorant += Q(1, 2) * radius ** (n + 2)
                assert norm_square(prefix) <= majorant**2
                assert majorant <= radius**2 / (2 * (1 - radius))
                total += 3
    assert total == 11322
    print(
        f"PASS {total}/{total} exact rational source coefficient, "
        "Euclidean finite triangle, and sharp geometric comparisons"
    )
    print(
        "BOUNDARY: rational controls only; no BishopSquareRootCalculus "
        "instance, Agda kernel receipt, or P1.N/Koenigs claim"
    )


if __name__ == "__main__":
    check()
