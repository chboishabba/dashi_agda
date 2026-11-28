#!/usr/bin/env python3
"""Independent exact finite diagnostics; NOT Agda kernel verification."""
from fractions import Fraction as Q
from math import factorial

count = 0
for k in range(1, 9):
    N = 2**k
    for m in range(k + 1):
        for n in range(k + 1):
            v = [0] * (N // 2)
            for j in range(N):
                r = ((m - n) * j) % N
                v[r % (N // 2)] += 1 if r < N // 2 else -1
            assert v == ([N] + [0] * (N // 2 - 1) if m == n else [0] * (N // 2))
            count += 1
print("exact dyadic cyclotomic mode checks:", count)
for n in range(81):
    s = sum((Q(1, 6)**j for j in range(1, n + 1)), Q(0))
    assert s == Q(1, 5) * (1 - Q(1, 6)**n)
    assert 4*s <= Q(4, 5)
print("exact geometric identities and bounds:", 162)
assert Q(2, 3)**2 + Q(1, 2)**2 == Q(25, 36) < Q(3, 4)
assert 6*(Q(1, 3) - Q(1, 64)) > Q(19, 10)
assert sum((Q(19, 10)**k / factorial(k) for k in range(5)), Q(0)) > 6
print("exact geometric reduction/radius inequalities:", 3)
print("TOTAL", count + 165)
