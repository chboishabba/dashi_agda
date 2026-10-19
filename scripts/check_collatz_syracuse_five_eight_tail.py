#!/usr/bin/env python3

from itertools import product


def bad_and_tail_counts(m: int, k: int) -> tuple[int, int]:
    bad = 0
    tail = 0
    for word in product((0, 1), repeat=m):
        ones = sum(word)
        if 2 * (3 ** ones) > 2 ** m:
            bad += 1
        if ones >= k:
            tail += 1
    return bad, tail


# Exhaustive range kept small enough for CI; the Agda theorem is universal.
for n in range(4):
    m = 8 * n + 1
    k = 5 * n + 1

    assert 2 * (3 ** (5 * n)) <= 2 ** m

    bad, tail = bad_and_tail_counts(m, k)
    assert bad <= tail
    assert (2 ** k) * tail <= 3 ** m
    assert (2 ** k) * bad <= 3 ** m

print('collatz five-eighths bad-word tail n<=3: PASS')
