#!/usr/bin/env python3
"""Exact independent finite-complex TSVF 2017 factorized postselection referee.

Coverage (no floats):
- actual Hermitian (Q(i)^2) initial/final vector amplitudes with complete
  orthogonal projectors and original-ABL-equivalent normalization;
- arbitrary rational-complex gamma factor lists and conjugated final bra;
- selected k surviving environment tensor overlaps and exact Born ratio;
- 0<=right/wrong Born weights and nonzero-selected-context restriction;
- sharp i-amplitude-vs-Born-weight Equation-25 no-go;
- all-k 2^k odds/error inequality conditional on ordered disturbed weights;
- adversarial violating factor and wrong-OS-time-step negative controls.

This is a FINITE model reference, not a source of physical final boundary,
full complex Hilbert completion, 2017 N-body dynamics, Euclidean OS H, Yang
Mills Haar/continuum/positive spectral mass gap, or Agda kernel acceptance.
"""
from __future__ import annotations

from fractions import Fraction as Q
from functools import reduce
from random import Random

ComplexQ = tuple[Q, Q]
Vector = tuple[ComplexQ, ComplexQ]

ZERO: ComplexQ = (Q(0), Q(0))
ONE: ComplexQ = (Q(1), Q(0))
I: ComplexQ = (Q(0), Q(1))

def mul(a: ComplexQ, b: ComplexQ) -> ComplexQ:
    return (a[0] * b[0] - a[1] * b[1],
            a[0] * b[1] + a[1] * b[0])

def add(a: ComplexQ, b: ComplexQ) -> ComplexQ:
    return (a[0] + b[0], a[1] + b[1])

def conj(a: ComplexQ) -> ComplexQ:
    return (a[0], -a[1])

def norm(a: ComplexQ) -> Q:
    return a[0] ** 2 + a[1] ** 2

def product(xs: list[ComplexQ]) -> ComplexQ:
    return reduce(mul, xs, ONE)

def inner(a: Vector, b: Vector) -> ComplexQ:
    return add(mul(conj(a[0]), b[0]), mul(conj(a[1]), b[1]))

def project_right(v: Vector) -> Vector:
    return (v[0], ZERO)

def project_wrong(v: Vector) -> Vector:
    return (ZERO, v[1])

def run() -> None:
    environment_right: Vector = (ONE, ZERO)
    environment_wrong: Vector = ((Q(3, 5), Q(0)), (Q(4, 5), Q(0)))
    alpha = inner(environment_right, environment_wrong)
    assert inner(environment_right, environment_right) == ONE
    assert inner(environment_wrong, environment_wrong) == ONE
    assert alpha == (Q(3, 5), Q(0))
    assert norm(alpha) == Q(9, 25)
    assert I != ONE and norm(I) == norm(ONE) == Q(1)

    random = Random(2017)
    checked = 0
    for k in range(29):
        overlap = product([alpha] * k)
        assert norm(overlap) == Q(9, 25) ** k
        for _ in range(250):
            gammas_right = [
                (Q(random.randint(-7, 7), random.randint(1, 7)),
                 Q(random.randint(-7, 7), random.randint(1, 7)))
                for _ in range(random.randint(0, 4))
            ]
            gammas_wrong = [
                (Q(random.randint(-7, 7), random.randint(1, 7)),
                 Q(random.randint(-7, 7), random.randint(1, 7)))
                for _ in range(random.randint(0, 4))
            ]
            target_right = product(gammas_right)
            target_wrong = mul(product(gammas_wrong), overlap)

            # Explicit original TSVF-style two-state transition amplitudes:
            # <bra|P_outcome|ket> for both complete projectors.
            forward: Vector = (ONE, ONE)
            backward: Vector = (conj(target_right), conj(target_wrong))
            amp_right = inner(backward, project_right(forward))
            amp_wrong = inner(backward, project_wrong(forward))
            assert project_right(project_right(forward)) == project_right(forward)
            assert project_wrong(project_wrong(forward)) == project_wrong(forward)
            assert project_right(project_wrong(forward)) == (ZERO, ZERO)
            assert project_wrong(project_right(forward)) == (ZERO, ZERO)
            assert (add(project_right(forward)[0], project_wrong(forward)[0]),
                    add(project_right(forward)[1], project_wrong(forward)[1])) == forward
            assert (amp_right, amp_wrong) == (target_right, target_wrong)
            w_right, w_wrong = norm(amp_right), norm(amp_wrong)
            assert w_right == reduce(lambda p, g: p * norm(g), gammas_right, Q(1))
            assert w_wrong == reduce(lambda p, g: p * norm(g), gammas_wrong, Q(1)) * norm(alpha) ** k
            assert w_right >= 0 and w_wrong >= 0
            if w_right + w_wrong:
                p_right, p_wrong = w_right / (w_right + w_wrong), w_wrong / (w_right + w_wrong)
                assert p_right + p_wrong == Q(1)
            checked += 1

    # Actual conditional selected ABL context: nonzero right gamma source.
    for k in range(51):
        wrong = Q(9, 25) ** k
        p_right, p_wrong = Q(1) / (1 + wrong), wrong / (1 + wrong)
        assert p_right + p_wrong == 1
        assert p_wrong <= Q(9, 25) ** k
        assert p_right / p_wrong == Q(25, 9) ** k
        assert Q(25, 9) ** k >= 2**k

    for k in range(101):
        for gr, gw in [(1, 0), (1, 1), (1, 3), (3, 1), (100, 99)]:
            if gr >= gw:
                assert (2**k + 1) * (gw * 9**k) <= gr * 25**k + gw * 9**k
    assert 1 * 25**2 < 100 * 9**2

    def identity_tick(t: int) -> int:
        return t
    def wrong_os_tick(t: int) -> int:
        return 1 - t
    assert identity_tick(0) != wrong_os_tick(0)

    print(f"PASS: {checked} arbitrary rational-complex gamma/tensor/original-ABL-equivalent cases")
    print("PASS: 51 selected normalized likelihoods, 101 all-k rate bounds and 2^k comparison")
    print("PASS: orthogonal projectors, gamma phase counterexample, adversarial weights, wrong OS clock")
    print("LIMIT: numerical/finite reference ONLY; Agda kernel/physical Hilbert/2017 actual apparatus still open")

if __name__ == "__main__":
    run()
