#!/usr/bin/env python3
"""Executable regression for the parametric integer parity-drift tail."""

from math import comb, log


def exact_bad_word_count(m: int) -> int:
    return sum(comb(m, k) for k in range(m + 1) if 2 * 3**k > 2**m)


def check_pair(a: int, b: int, max_n: int = 2) -> None:
    assert 3**a <= 2**b, (a, b)
    for n in range(max_n + 1):
        m = b * n + 1
        threshold = a * n + 1
        bad = exact_bad_word_count(m)
        assert 2**threshold * bad <= 3**m, (a, b, n, bad)


# Source-written Agda instances.
check_pair(5, 8)
check_pair(17, 27)

# Numerical search confirms the generic theorem covers progressively sharper
# lower rational approximants to log_3(2); these do not need separate Agda
# theorem bodies because the parametric theorem consumes only 3^a <= 2^b.
alpha = log(2, 3)
best = []
last = -1.0
for b in range(1, 101):
    a = max(k for k in range(b + 1) if 3**k <= 2**b)
    ratio = a / b
    if ratio > last:
        best.append((a, b))
        last = ratio

assert (5, 8) in best
assert (17, 27) in best
assert (29, 46) in best
assert (41, 65) in best
assert 41 / 65 < alpha

print("collatz syracuse rational drift tail regression: PASS")
print("record approximants:", best)
