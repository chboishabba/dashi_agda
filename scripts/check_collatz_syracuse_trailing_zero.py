#!/usr/bin/env python3
from itertools import product


def affine_additive(bits):
    if not bits:
        return 0
    head, *tail = bits
    tail = tuple(tail)
    if head == 0:
        return 2 * affine_additive(tail)
    return 3 ** sum(tail) + 2 * affine_additive(tail)


for m in range(0, 11):
    for word in product((0, 1), repeat=m):
        extended = word + (0,)
        assert sum(extended) == sum(word)
        assert affine_additive(extended) == affine_additive(word)

        p = 3 ** sum(word)
        old_gap = 2**m - p
        if old_gap > 0:
            new_gap = old_gap + (p + old_gap)
            assert 2 ** (m + 1) == p + new_gap
            assert new_gap >= old_gap

print("collatz syracuse trailing-zero certificate checks: PASS")
