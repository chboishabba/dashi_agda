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
    # 3^a m == 3 mod 4.
    return 3 if a % 2 == 0 else 1


def first_ge_in_mod4(lower: int, residue: int) -> int:
    return lower + ((residue - lower) % 4)


def optimized_cutoff(U: int) -> tuple[int, tuple[int, int, int]]:
    """Largest N-1 before the first unavailable odd-run request.

    Returns (cutoff, (a,m,v)) where 2^a*m is the first missing seed scale and
    36*v+27 = 3^a*m.
    """
    threshold = 36 * U + 27
    best_seed = 16 * U + 12  # safe initial upper bound; a=2 search improves.
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
    """0=no certificate, 1=direct merge, 2=contracting pair return."""
    x, j = iter_with_odd_count(3 * residue + 2, depth)
    y, k = iter_with_odd_count(27 * residue + 20, depth)

    # Same all-quotient slope and same base endpoint.
    if x == y and j == k + 2:
        return 1

    # Return to (3v+2,27v+20) with v smaller for every quotient.
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


# Reproduce the externally kernel-certified request cutoffs.
assert optimized_cutoff(61) == (415, (5, 13, 87))
assert optimized_cutoff(415) == (511, (9, 1, 546))
assert optimized_cutoff(511) == (511, (9, 1, 546))

# The first stalled request is not a true transfer obstruction.
assert 3**9 == 36 * 546 + 27
assert first_below(27 * 546 + 20, 511) == (7, 346)

# Literal target stopping certificate used by the Agda barrier owner.
y = 27 * 546 + 20
for _ in range(30):
    y = syracuse(y)
assert y == 1

# Independent semantic reproduction of the published paired-cylinder frontier.
survivors, merge_nodes, return_nodes = adaptive_pair_census(18)
assert survivors == 230_701
assert merge_nodes == 2_757
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
