#!/usr/bin/env python3
"""Executable calibration for the affine-transfer max-cut.

External cross-pollination source (claims/census semantics only):
Michael Sharpe, msharpe248/collatz @
ec8174b567d5cab4960024782210b5f5db02bd3a,
notably RequestCutoff.lean and AffinePairReturn.lean.

This script independently recomputes the stated finite objects using DASHI's
shortcut-Syracuse convention.  It is calibration, not proof transport and not
a proof of the Collatz conjecture.
"""


def syracuse(n: int) -> int:
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def iter_with_odd_count(n: int, steps: int) -> tuple[int, int]:
    odd = 0
    for _ in range(steps):
        odd += n & 1
        n = syracuse(n)
    return n, odd


def required_mod4(a: int) -> int:
    return 3 if a % 2 == 0 else 1


def first_ge_in_mod4(lower: int, residue: int) -> int:
    return lower + ((residue - lower) % 4)


def optimized_cutoff(U: int) -> tuple[int, tuple[int, int, int]]:
    threshold = 36 * U + 27
    best_seed = 16 * U + 12
    best = None
    a = 2
    while (1 << a) <= best_seed + 1:
        p3 = 3**a
        m0 = (threshold + p3 - 1) // p3
        m = max(1, first_ge_in_mod4(m0, required_mod4(a)))
        seed_scale = (1 << a) * m
        v = (p3 * m - 27) // 36
        if seed_scale < best_seed:
            best_seed = seed_scale
            best = (a, m, v)
        a += 1
    assert best is not None
    return best_seed - 1, best


def first_below(n: int, bound: int, cap: int = 10000) -> tuple[int, int] | None:
    for t in range(cap + 1):
        if n < bound:
            return t, n
        n = syracuse(n)
    return None


def pair_certificate(residue: int, depth: int) -> int:
    x, j = iter_with_odd_count(3 * residue + 2, depth)
    y, k = iter_with_odd_count(27 * residue + 20, depth)
    if x == y and j == k + 2:
        return 1
    if j == k and y == 9 * x + 2 and x % 3 == 2:
        v = (x - 2) // 3
        if v < residue and 3**j <= 2**depth:
            return 2
    return 0


def adaptive_pair_census(max_depth: int = 18) -> tuple[int, int, int]:
    survivors = [0]
    total_merge = 0
    total_return = 0
    for depth in range(1, max_depth + 1):
        half = 1 << (depth - 1)
        nxt = []
        for parent in survivors:
            for residue in (parent, parent + half):
                cert = pair_certificate(residue, depth)
                if cert == 1:
                    total_merge += 1
                elif cert == 2:
                    total_return += 1
                else:
                    nxt.append(residue)
        survivors = nxt
    return len(survivors), total_merge, total_return


assert optimized_cutoff(61) == (415, (5, 13, 87))
assert optimized_cutoff(415) == (511, (9, 1, 546))
assert optimized_cutoff(511) == (511, (9, 1, 546))

assert 3**9 == 36 * 546 + 27
assert first_below(27 * 546 + 20, 511) == (7, 346)

y = 27 * 546 + 20
for _ in range(30):
    y = syracuse(y)
assert y == 1

survivors, merge_nodes, return_nodes = adaptive_pair_census(18)
assert survivors == 230_701
assert merge_nodes == 2_754
assert return_nodes == 482

print("collatz syracuse affine-transfer calibration: PASS")
print("cutoff 61 -> 415; cutoff 415/511 -> 511; first request v=546")
print("A(546) target: 14762 -> 346 in 7 steps -> 1 in 30 steps")
print(
    "adaptive pair depth 18:",
    f"survivors={survivors}",
    f"merge_nodes={merge_nodes}",
    f"return_nodes={return_nodes}",
)
