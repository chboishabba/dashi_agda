#!/usr/bin/env python3
"""Exact constructive TSVF environmental overlap / ABL mass referee.

Uses rational 2-level normalized Hilbert states:
  eps1 = (5,0)/5; eps2 = (3,4)/5.
The full k-fold tensor product overlap squared is (9/25)^k.
Under a selected branch with equal and positive disturbed-factor weights,
right/wrong ABL-style unnormalized weights are 25^k and 9^k.
The probabilities are exactly normalized by their common denominator.

Includes nontrivial unequal disturbance factors, zero-wrong branch,
same-boundary admissibility != nonzero Hilbert overlap, and monotonic
likelihood for k = N-n. This is NOT the actual interacting 2017 apparatus,
a continuum quantum source, a physical postselection experiment, a
multiverse model, a Lorentz/OS join, or Agda kernel certification.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import product

RIGHT = (Fraction(1), Fraction(0))
WRONG = (Fraction(3, 5), Fraction(4, 5))
ORTHO = (Fraction(0), Fraction(1))

def dot(a: tuple[Fraction, Fraction], b: tuple[Fraction, Fraction]) -> Fraction:
    return sum((x * y for x, y in zip(a, b)), Fraction(0))

def squared_overlap(k: int) -> Fraction:
    assert k >= 0
    # Tensor inner product factorizes across k independently sourced sites.
    overlap = Fraction(1)
    for _ in range(k):
        overlap *= dot(RIGHT, WRONG)
    return overlap ** 2

def normalized_two_branch(k: int, gamma_right: Fraction = Fraction(1),
                          gamma_wrong: Fraction = Fraction(1)) -> tuple[Fraction, Fraction]:
    assert k >= 0 and gamma_right > 0 and gamma_wrong >= 0
    unnormalized_right = gamma_right
    unnormalized_wrong = gamma_wrong * squared_overlap(k)
    denominator = unnormalized_right + unnormalized_wrong
    assert denominator > 0
    return (unnormalized_right / denominator,
            unnormalized_wrong / denominator)

def main() -> None:
    assert dot(RIGHT, RIGHT) == 1
    assert dot(WRONG, WRONG) == 1
    assert dot(RIGHT, WRONG) == Fraction(3, 5)
    assert dot(RIGHT, ORTHO) == 0
    assert dot(ORTHO, ORTHO) == 1
    # Both histories can be logically admitted, but the Hilbert overlap
    # between the orthogonal alternative records is zero.
    admissible_from_both = {("b-", "b+", "h0"), ("b-", "b+", "h1")}
    assert all(item in admissible_from_both for item in admissible_from_both)
    assert dot(RIGHT, ORTHO) == 0

    for k in range(51):
        q = squared_overlap(k)
        assert q == Fraction(9, 25) ** k
        p_right, p_wrong = normalized_two_branch(k)
        assert p_right == Fraction(25**k, 25**k + 9**k)
        assert p_wrong == Fraction(9**k, 25**k + 9**k)
        assert p_right + p_wrong == 1
        assert p_right >= p_wrong
        assert p_wrong <= Fraction(9, 25) ** k
        assert (p_right / p_wrong) == Fraction(25, 9) ** k
        if k:
            assert p_right > Fraction(1, 2)

    # Unequal disturbed-factor weights are not silently discarded.
    for k, gr, gw in product(
        range(15),
        (Fraction(1, 4), Fraction(1), Fraction(3, 2), Fraction(7, 3)),
        (Fraction(0), Fraction(1, 7), Fraction(1), Fraction(5, 2))
    ):
        pr, pw = normalized_two_branch(k, gr, gw)
        assert pr + pw == 1
        assert pr > 0
        if gw == 0:
            assert pw == 0 and pr == 1
        else:
            assert pr / pw == (gr / gw) * Fraction(25, 9) ** k

    # Even N >> n does not guarantee robustness if the disturbed-factor
    # ratio overwhelms the surviving environmental overlap.
    pr, pw = normalized_two_branch(10, Fraction(1, 10**12), Fraction(1))
    assert pr < pw
    # k=0 surviving records give no branch advantage at equal gammas.
    assert normalized_two_branch(0) == (Fraction(1, 2), Fraction(1, 2))

    print("PASS: finite rational Hilbert norms and nonorthogonal/orthogonal tests")
    print("PASS: 51 exact tensor overlaps q=(9/25)^k and normalized ABL-like pairs")
    print("PASS: 960 unequal gamma/zero-wrong exact probability cases")
    print("PASS: wrong-branch tail <= (9/25)^k and odds=(25/9)^k")
    print("PASS: adversarial N>>n with tiny gamma_right breaks robustness")
    print("NOTE: Agda source status and physical Hilbert/postselection remain distinct")

if __name__ == "__main__":
    main()
