#!/usr/bin/env python3
"""Exact-rational negative controls for the 2026-11-12 four-Clay attachment.
Tests do not constitute kernel acceptance or a Clay proof."""
from fractions import Fraction as Q


def product(p, q):
    result = [Q(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            result[i+j] += a*b
    return result


def integral_even_unit(p):
    return sum((2*a/(k+1) for k, a in enumerate(p) if k % 2 == 0), Q(0))


def shift(p, k):
    return [Q(0)]*k + p


def derivative(p):
    return [k*p[k] for k in range(1, len(p))]


def rh_signed_fifth_counterexample():
    # C^1 even H=(1-x^2)^2 on [-1,1], zero elsewhere.
    h = [Q(1), Q(0), Q(-2), Q(0), Q(1)]
    squared = product(h, h)
    m2 = integral_even_unit(shift(squared, 2))
    m3 = integral_even_unit(shift(squared, 3))
    m4 = integral_even_unit(shift(squared, 4))
    derivative_term = integral_even_unit(shift(product(h, derivative(h)), 5))
    delta = derivative_term - m2*m3
    assert m3 == 0
    assert m4 == Q(256, 15015)
    assert derivative_term == -Q(5, 2)*m4
    assert delta == -Q(128, 3003) < 0
    return delta


def ns_young_exponent_counterexamples():
    # delta=A=nu=1, B=n^2; claimed B^(5/2) <= B^2/2 + C.
    for C in [Q(0), Q(1), Q(5), Q(100), Q(10000)]:
        n = int(C) + 2
        assert Q(n**5) > Q(n**4, 2)+C


def ns_integrability_counterexample():
    # A(t)=t^(-3/4): integral A finite (=4);
    # integral A^(3/2)= integral t^(-9/8) diverges.
    exponent = Q(3, 4)
    assert exponent < 1 <= Q(3, 2)*exponent
    assert 1/(1-exponent) == 4


def pnp_fixed_input_quantifier_counterexample():
    for correct_bit in [False, True]:
        constant_deciders = [lambda _: False, lambda _: True]
        assert any(d("fixed formula") == correct_bit for d in constant_deciders)


def ym_signed_interval_and_shifted_denominator():
    hull = [num/den for num in [Q(-2), Q(1)]
            for den in [Q(2), Q(4)]]
    assert min(hull) == -1 and max(hull) == Q(1, 2)
    # q=pi, p=-pi: shifted momentum zero despite outer q.
    assert Q(1)+Q(-1) == 0


if __name__ == "__main__":
    delta = rh_signed_fifth_counterexample()
    ns_young_exponent_counterexamples()
    ns_integrability_counterexample()
    pnp_fixed_input_quantifier_counterexample()
    ym_signed_interval_and_shifted_denominator()
    print("PASS: 5 source-specific exact-rational negative-control groups")
    print("RH selected compact even H: Delta5 =", delta)
    print("No Clay endpoint promoted.")
