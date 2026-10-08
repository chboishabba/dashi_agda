#!/usr/bin/env python3
"""Finite calibration of exact complete-block parity-word uniformity.

For each m <= 10, sample the literal positive starts 1..2^m.  The test checks
that their first m shortcut-Syracuse parity bits enumerate every BinaryWord m
exactly once, and that the Hamming-weight histogram is the exact binomial row.

This is regression/calibration evidence, not a replacement for the general Agda
cylinder-bijection and complete-block counting theorems.
"""
from itertools import product
from math import comb


def shortcut(x: int) -> int:
    return x // 2 if x % 2 == 0 else (3 * x + 1) // 2


def parity_word(x: int, m: int) -> tuple[int, ...]:
    out: list[int] = []
    for _ in range(m):
        out.append(x & 1)
        x = shortcut(x)
    return tuple(out)


def main() -> None:
    for m in range(0, 11):
        block_size = 1 << m
        words = [parity_word(x, m) for x in range(1, block_size + 1)]
        expected_words = set(product((0, 1), repeat=m))

        assert len(words) == block_size
        assert set(words) == expected_words
        assert len(set(words)) == block_size

        histogram = [0] * (m + 1)
        for word in words:
            histogram[sum(word)] += 1
        assert histogram == [comb(m, k) for k in range(m + 1)]

    print("collatz syracuse complete-block calibration: PASS (m <= 10)")


if __name__ == "__main__":
    main()
