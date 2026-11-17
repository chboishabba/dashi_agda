#!/usr/bin/env python3
"""Exact finite diagnostics for the sharp Collatz/Syracuse affine barrier.

This script is regression / conjecture-generation evidence only.  It checks
integer identities used by the Agda source owners and deliberately does not
promote finite coefficient-stopping agreement to a universal theorem.
"""

from __future__ import annotations

from itertools import product


def shortcut(x: int) -> int:
    return x // 2 if x % 2 == 0 else (3 * x + 1) // 2


def affine_additive(word: tuple[int, ...]) -> int:
    if not word:
        return 0
    head, tail = word[0], word[1:]
    tail_a = affine_additive(tail)
    if head == 0:
        return 2 * tail_a
    return 3 ** sum(tail) + 2 * tail_a


def gap(word: tuple[int, ...]) -> int:
    return 2 ** len(word) - 3 ** sum(word)


def barrier(word: tuple[int, ...]) -> int | None:
    g = gap(word)
    return None if g <= 0 else affine_additive(word) // g


def threshold(word: tuple[int, ...]) -> int | None:
    b = barrier(word)
    return None if b is None else b + 1


def append_zero(word: tuple[int, ...]) -> tuple[int, ...]:
    return word + (0,)


def append_one(word: tuple[int, ...]) -> tuple[int, ...]:
    return word + (1,)


def orbit_prefix(x: int, m: int) -> tuple[tuple[int, ...], int]:
    y = x
    bits: list[int] = []
    for _ in range(m):
        bits.append(y & 1)
        y = shortcut(y)
    return tuple(bits), y


def first_descent_coordinates(x: int, cap: int = 100_000) -> tuple[int, int, int, int, int]:
    y = x
    bits: list[int] = []
    for m in range(1, cap + 1):
        bits.append(y & 1)
        y = shortcut(y)
        if y < x:
            word = tuple(bits)
            a = affine_additive(word)
            g = gap(word)
            assert g > 0
            return m, sum(word), a, g, a // g
    raise RuntimeError((x, cap))


def first_contracting_horizon(x: int, cap: int = 100_000) -> int:
    y = x
    ones = 0
    for m in range(1, cap + 1):
        ones += y & 1
        y = shortcut(y)
        if 2**m > 3**ones:
            return m
    raise RuntimeError((x, cap))


def first_descent_horizon(x: int, cap: int = 100_000) -> int:
    y = x
    for m in range(1, cap + 1):
        y = shortcut(y)
        if y < x:
            return m
    raise RuntimeError((x, cap))


def check_sharp_thresholds(max_length: int = 12) -> None:
    for m in range(max_length + 1):
        for word in product((0, 1), repeat=m):
            g = gap(word)
            if g <= 0:
                continue
            a = affine_additive(word)
            n = threshold(word)
            assert n is not None
            assert a < g * n
            for candidate in range(n):
                assert not (a < g * candidate)

    assert threshold((1, 1, 0, 0)) == 1
    assert threshold((1, 1, 0, 1, 0)) == 5
    assert threshold((1, 1, 1, 0, 0)) == 4


def check_prefix_recurrence(max_length: int = 12) -> None:
    for m in range(max_length + 1):
        for word in product((0, 1), repeat=m):
            a = affine_additive(word)
            s = sum(word)
            d = 2**m
            multiplier = 3**s

            zero = append_zero(word)
            assert affine_additive(zero) == a
            assert sum(zero) == s
            assert 2 ** len(zero) == 2 * d

            one = append_one(word)
            assert affine_additive(one) == 3 * a + d
            assert sum(one) == s + 1
            assert 3 ** sum(one) == 3 * multiplier
            assert 2 ** len(one) == 2 * d

            g = d - multiplier
            if g > 0:
                next_gap = gap(one)
                expected = 2 * g - multiplier
                assert next_gap == expected
                if multiplier < 2 * g:
                    assert next_gap > 0
                elif multiplier == 2 * g:
                    assert next_gap == 0
                else:
                    assert next_gap < 0

                # Late even steps preserve A and enlarge positive gap, hence
                # the exact floor(A/g) barrier cannot increase.
                assert gap(zero) > g
                assert barrier(zero) <= barrier(word)


def check_literal_affine_escape(limit: int = 5_000, depth: int = 64) -> None:
    for x in range(1, limit + 1):
        y = x
        bits: list[int] = []
        for m in range(1, depth + 1):
            bits.append(y & 1)
            y = shortcut(y)
            word = tuple(bits)
            a = affine_additive(word)
            g = gap(word)
            assert (2**m) * y == (3 ** sum(word)) * x + a
            if g > 0:
                assert (a < g * x) == (y < x)
                if y >= x:
                    assert x <= a // g


def check_finite_coefficient_stopping_agreement(limit: int = 200_000) -> None:
    """Finite CST diagnostic only; NOT authority for the open universal claim."""
    for x in range(2, limit):
        coefficient = first_contracting_horizon(x)
        descent = first_descent_horizon(x)
        if coefficient != descent:
            raise AssertionError((x, coefficient, descent))


def main() -> None:
    check_sharp_thresholds()
    check_prefix_recurrence()
    check_literal_affine_escape()
    check_finite_coefficient_stopping_agreement()

    records = [2, 3, 7, 27, 703, 10087, 35655]
    rows = [(x, *first_descent_coordinates(x)) for x in records]
    expected = [
        (2, 1, 0, 0, 1, 0),
        (3, 4, 2, 5, 7, 0),
        (7, 7, 4, 73, 47, 1),
        (27, 59, 37, 1100931843921811423, 126176846412426125, 8),
        (703, 81, 51, 4363973393857133714501915, 264157676153700583101605, 16),
        (10087, 105, 66, 142211808132923543919421901584993, 9661664824670728485973860768503, 14),
        (35655, 135, 85, 128297408958579634095795478197521347382875, 7638597418194063957503729671115189749325, 16),
    ]
    assert rows == expected, rows

    print("PASS: sharp floor(A/g)+1 threshold/minimality checked through depth 12")
    print("PASS: late-bit A/s/g recurrence checked through depth 12")
    print("PASS: literal affine escape equivalence checked for x<=5000, m<=64")
    print("PASS: first coefficient/descent horizons agree for 2<=x<200000 (finite diagnostic only)")
    print("first-descent record coordinates (x,m,s,A,g,floor(A/g)):")
    for row in rows:
        print(" ", row)
    print("NOTE: the finite coefficient-stopping agreement is not promoted to Terras/CST universality")


if __name__ == "__main__":
    main()
