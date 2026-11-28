#!/usr/bin/env python3
"""Exact finite controls for the original two-cut composition proof.

Not a proof of infinite convergence or an Agda kernel acceptance receipt.
"""
from fractions import Fraction as F
from random import Random
from sympy import symbols, expand, __version__


def mul(a, b):
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def prefix(a, n):
    return sum(a[:n], F(0))


rng = Random(369)
count = 0
for q in map(F, ['0', '1/5', '-1/5', '1/2', '-1/2', '1']):
    for case in range(5):
        b = [F(0)] + [F(rng.randrange(-4, 5), rng.randrange(2, 8)) for _ in range(4)]
        c = [F(rng.randrange(-4, 5), rng.randrange(2, 8)) for _ in range(7)]
        u = [x * q**n for n, x in enumerate(b)]
        B, v = sum(map(abs, u)), sum(u)
        powers = [[F(1)]]
        for _ in range(1, len(c)):
            powers.append(mul(u, powers[-1]))
        target = sum(c[k] * v**k for k in range(len(c)))
        m = [abs(c[k]) * B**k for k in range(len(c))]
        full = [F(0)] * len(powers[-1])
        positive = [F(0)] * len(full)
        for k, p in enumerate(powers):
            assert sum(p) == v**k
            assert sum(map(abs, p)) <= B**k
            for n, a in enumerate(p):
                assert n >= k or a == 0
                full[n] += c[k] * a
                positive[n] += abs(c[k]) * abs(a)
        assert all(abs(a) <= p for a, p in zip(full, positive))
        assert sum(positive) <= sum(m)
        for N in range(len(full) + 2):
            D = sum(c[k] * prefix(powers[k], N) for k in range(min(N, len(c))))
            A = sum(abs(c[k]) * prefix(list(map(abs, powers[k])), N)
                    for k in range(min(N, len(c))))
            assert D == prefix(full, N)
            assert A == prefix(positive, N)
            assert abs(D) <= A <= sum(m)
            for M in range(min(N, len(c)) + 1):
                R = sum(c[k] * prefix(powers[k], N) for k in range(M))
                L = sum(c[k] * v**k for k in range(M))
                tail = sum(m[M:])
                assert abs(D - R) <= tail
                assert abs(target - L) <= tail
                assert abs(D - target) <= abs(R - L) + 2 * tail
                count += 1
print(f'{count} signed rational two-cut controls PASS')

# Exact scalar norm budget from the existing CM tail owner.
a, b = F(1, 25), F(2, 25)
T = (1 + a)**3 - 1
assert T < 1
Z = (T + (1 + b)**2 - 1) / (1 - T)
# The earlier bound using (1-a)^3 is sharper than this crude reciprocal.
# The l1 geometric inverse uses 1/(1-T), not 1/(1-a)^3.
assert Z == F(1517, 4558)
assert Z < F(1, 3)
print('CM l1 geometric-inverse budget:', Z, '< 1/3 PASS')

# Literal hypergeometric coefficient ratio: positivity and a strict
# contraction below one for every nonnegative integer degree.
n = symbols('n', nonnegative=True)
diff = expand((n+1)**3 - (n+F(1,6))*(n+F(1,2))*(n+F(5,6)))
assert all(x > 0 for x in diff.as_poly(n).all_coeffs())
h = F(1)
for k in range(256):
    ratio = (k+F(1,6))*(k+F(1,2))*(k+F(5,6))/(k+1)**3
    assert 0 < ratio < 1
    h *= ratio
    assert 0 < h <= 1
print('256 hypergeometric ratios and symbolic positive difference PASS; SymPy', __version__)
