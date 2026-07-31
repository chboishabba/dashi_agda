#!/usr/bin/env python3
"""Independent finite oracle for the explicit ternary-Golay/UBP table tranche."""

from __future__ import annotations

from collections import Counter
from fractions import Fraction
from itertools import combinations, product

A = (
    (2, 0, 2, 1, 1, 2),
    (2, 1, 1, 2, 0, 2),
    (2, 2, 0, 2, 1, 1),
    (2, 2, 1, 1, 2, 0),
    (2, 1, 2, 0, 2, 1),
    (0, 1, 1, 1, 1, 1),
)

SOURCE_PI_CF_50 = (
    3, 7, 15, 1, 292, 1, 1, 1, 2, 1,
    3, 1, 14, 2, 1, 1, 2, 2, 2, 2,
    1, 84, 2, 1, 1, 15, 3, 13, 1, 4,
    2, 6, 6, 99, 1, 2, 2, 6, 3, 5,
    1, 1, 6, 8, 1, 7, 1, 6, 1, 99,
)

CANONICAL_PI_CF_51 = (
    3, 7, 15, 1, 292, 1, 1, 1, 2, 1,
    3, 1, 14, 2, 1, 1, 2, 2, 2, 2,
    1, 84, 2, 1, 1, 15, 3, 13, 1, 4,
    2, 6, 6, 99, 1, 2, 2, 6, 3, 5,
    1, 1, 6, 8, 1, 7, 1, 2, 3, 7,
    1,
)


def encode(message: tuple[int, ...]) -> tuple[int, ...]:
    parity = tuple(
        sum(message[row] * A[row][column] for row in range(6)) % 3
        for column in range(6)
    )
    return message + parity


def dot(left: tuple[int, ...], right: tuple[int, ...]) -> int:
    return sum(a * b for a, b in zip(left, right, strict=True)) % 3


def convergent(coefficients: tuple[int, ...]) -> Fraction:
    p_prev_prev, p_prev = 0, 1
    q_prev_prev, q_prev = 1, 0
    for coefficient in coefficients:
        p_prev_prev, p_prev = p_prev, coefficient * p_prev + p_prev_prev
        q_prev_prev, q_prev = q_prev, coefficient * q_prev + q_prev_prev
    return Fraction(p_prev, q_prev)


def observer_constant(pi_approximation: Fraction) -> Fraction:
    return pi_approximation / (pi_approximation * pi_approximation + 2)


def main() -> None:
    messages = list(product(range(3), repeat=6))
    codewords = [encode(message) for message in messages]

    assert len(messages) == 729
    assert len(set(codewords)) == 729
    assert all(codeword[:6] == message for message, codeword in zip(messages, codewords, strict=True))

    basis = [encode(tuple(1 if i == row else 0 for i in range(6))) for row in range(6)]
    assert all(dot(left, right) == 0 for left in basis for right in basis)

    weight_distribution = Counter(sum(value != 0 for value in word) for word in codewords)
    assert weight_distribution == Counter({9: 440, 6: 264, 12: 24, 0: 1})

    hexads = {
        frozenset(index for index, value in enumerate(word) if value != 0)
        for word in codewords
        if sum(value != 0 for value in word) == 6
    }
    assert len(hexads) == 132
    assert all(len(hexad) == 6 for hexad in hexads)

    pentads = [frozenset(indices) for indices in combinations(range(12), 5)]
    assert len(pentads) == 792
    containing_counts = Counter(
        sum(pentad <= hexad for hexad in hexads)
        for pentad in pentads
    )
    assert containing_counts == Counter({1: 792})

    canonical50 = CANONICAL_PI_CF_51[:50]
    assert SOURCE_PI_CF_50[:47] == canonical50[:47]
    assert SOURCE_PI_CF_50[47] == 6
    assert canonical50[47] == 2
    assert SOURCE_PI_CF_50 != canonical50

    source_pi50 = convergent(SOURCE_PI_CF_50)
    canonical_pi50 = convergent(canonical50)
    canonical_pi51 = convergent(CANONICAL_PI_CF_51)

    assert source_pi50 == Fraction(
        183157143516396120473427579101,
        58300729506452262642556705291,
    )
    assert canonical_pi50 == Fraction(
        16397605394050964443746106649,
        5219519906667074477262822481,
    )
    assert canonical_pi51 == Fraction(
        18644210947563865148979297792,
        5934636664705637943635533097,
    )
    assert canonical_pi50.denominator * canonical_pi51.denominator == (
        30975954210267369528087864730966858500331494237311153657
    )

    assert observer_constant(source_pi50) == Fraction(
        10678195081323867029398952980491706367345312803032847723391,
        40344489343054752407088436891842371820968160890283666757563,
    )
    assert observer_constant(canonical_pi50) == Fraction(
        85587627775920406939229606214235442123216034256580776169,
        323368238771197016635670695332535842359492259206719999923,
    )

    print("Explicit ternary Golay oracle passed.")
    print("  729 distinct codewords; weights 0/6/9/12 = 1/264/440/24")
    print("  132 distinct hexads; all 792 pentads have one containing hexad")
    print("  UBP/canonical pi tables first differ at one-based coefficient 48")


if __name__ == "__main__":
    main()
