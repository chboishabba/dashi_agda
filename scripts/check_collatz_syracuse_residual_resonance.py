#!/usr/bin/env python3
"""Finite diagnostic for the Collatz/Syracuse residual-resonance max-cut.

This script is exploratory/regression evidence only.  Agda theorem owners remain
formal authority.  In particular, finite agreement, record searches, and
floating ranking of exact integer gaps do not promote to universal stopping.
"""

from __future__ import annotations

from math import log


def shortcut_syracuse(x: int) -> int:
    return x // 2 if x % 2 == 0 else (3 * x + 1) // 2


def parity_word(x: int, m: int) -> tuple[int, ...]:
    out: list[int] = []
    y = x
    for _ in range(m):
        out.append(y & 1)
        y = shortcut_syracuse(y)
    return tuple(out)


def affine_additive_term(word: tuple[int, ...]) -> int:
    if not word:
        return 0
    head, tail = word[0], word[1:]
    tail_a = affine_additive_term(tail)
    if head == 0:
        return 2 * tail_a
    return 3 ** sum(tail) + 2 * tail_a


def coefficient_gap(word: tuple[int, ...]) -> int:
    return 2 ** len(word) - 3 ** sum(word)


def first_descent(x: int, cap: int = 10_000) -> int:
    y = x
    for m in range(1, cap + 1):
        y = shortcut_syracuse(y)
        if y < x:
            return m
    raise RuntimeError(f"no descent found below cap={cap} for x={x}")


def check_affine_identity(limit: int = 2_000, depth: int = 32) -> None:
    for x in range(1, limit + 1):
        y = x
        word: list[int] = []
        for m in range(1, depth + 1):
            word.append(y & 1)
            y = shortcut_syracuse(y)
            w = tuple(word)
            lhs = (2**m) * y
            rhs = (3 ** sum(w)) * x + affine_additive_term(w)
            if lhs != rhs:
                raise AssertionError((x, m, lhs, rhs, w))


def check_same_count_correction_collision() -> None:
    left = (1, 1, 0, 1, 0)   # 11010
    right = (1, 0, 1, 1, 0)  # 10110
    assert sum(left) == sum(right) == 3
    assert coefficient_gap(left) == coefficient_gap(right) == 5
    assert affine_additive_term(left) == 23
    assert affine_additive_term(right) == 29
    assert affine_additive_term(left) != affine_additive_term(right)


def first_descent_records(limit: int = 200_000) -> list[tuple[int, int]]:
    records: list[tuple[int, int]] = []
    best = 0
    for x in range(2, limit):
        horizon = first_descent(x)
        if horizon > best:
            best = horizon
            records.append((x, horizon))
    return records


def closest_positive_coefficient_gaps(max_length: int = 64) -> list[tuple[float, int, int, int]]:
    rows: list[tuple[float, int, int, int]] = []
    for m in range(1, max_length + 1):
        for s in range(m + 1):
            gap = 2**m - 3**s
            if gap > 0:
                rows.append((gap / (2**m), m, s, gap))
    rows.sort()
    return rows


def main() -> None:
    check_affine_identity()
    check_same_count_correction_collision()

    records = first_descent_records()
    expected_records = [
        (2, 1),
        (3, 4),
        (7, 7),
        (27, 59),
        (703, 81),
        (10087, 105),
        (35655, 135),
    ]
    assert records == expected_records, records

    near = closest_positive_coefficient_gaps()
    expected_leaders = [(46, 29), (27, 17), (8, 5)]
    assert [(m, s) for _, m, s, _ in near[:3]] == expected_leaders

    alpha = log(2) / log(3)
    print("PASS: literal affine identity checked for x<=2000, m<=32")
    print("PASS: same odd-count collision has A=23 versus A=29 at gap=5")
    print(f"log_3(2) diagnostic={alpha:.15f}")
    print("first-descent record starts below 200000:", records)
    print("closest positive exact coefficient gaps for m<=64:")
    for relative, m, s, gap in near[:10]:
        print(f"  m={m:2d} s={s:2d} s/m={s/m:.12f} gap={gap} relative={relative:.12g}")
    print("NOTE: floating ratios rank exact integer gaps only; they are not formal proof inputs")


if __name__ == "__main__":
    main()
