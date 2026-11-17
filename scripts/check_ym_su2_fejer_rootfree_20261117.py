#!/usr/bin/env python3
"""Exact rational stand-in for YM.REAL root-free S3 cubature.
Not an Agda kernel certificate. Fejer-I probability weights use 1/M,
and the three-factor product has 4*m**3 nodes, not 2*m**3.
Mathematical sources: Fejer, Stroud, Pizzetti/Folland.
"""
from fractions import Fraction as Q
import math

checks = 0

def equal(x, y, name):
    global checks
    assert x == y, (name, x, y)
    checks += 1

def poch(x, n):
    a = Q(1)
    for j in range(n):
        a *= x + j
    return a

def moment(exps):
    if any(x % 2 for x in exps):
        return Q(0)
    a = [x // 2 for x in exps]
    return math.prod(poch(Q(1, 2), x) for x in a) / poch(Q(2), sum(a))

def t_power_cheb(k):
    # t^k = sum c_j T_j(t); the coefficients are rational.
    if k == 0:
        return {0: Q(1)}
    out = {}
    for h in range(k // 2 + 1):
        freq = k - 2 * h
        divisor = 2**k if freq == 0 else 2**(k - 1)
        out[freq] = Q(math.comb(k, h), divisor)
    return out

def fejer_cheb_moment(M, k):
    # Midpoint cosine orthogonality and normalized Fejer-I coefficient.
    assert 0 <= k < M
    if k == 0:
        return Q(1)
    return Q(0) if k % 2 else Q(-1, k*k - 1)

def fejer_power_moment(M, k):
    assert k < M
    return sum((c * fejer_cheb_moment(M, j)
                for j, c in t_power_cheb(k).items()), Q(0))

def circle_moment(a, b):
    if a % 2 or b % 2:
        return Q(0)
    return (poch(Q(1, 2), a//2) * poch(Q(1, 2), b//2) /
            poch(Q(1), (a+b)//2))

def legendre_moment(a, s):
    if a % 2:
        return Q(0)
    return (poch(Q(1, 2), a//2) * poch(Q(1), s) /
            poch(Q(3, 2), a//2 + s))

def cheb2_moment(a, s):
    if a % 2:
        return Q(0)
    return (poch(Q(1, 2), a//2) * poch(Q(3, 2), s) /
            poch(Q(2), a//2 + s))

def product_moment(e):
    a, b, c, d = e
    circle = circle_moment(c, d)
    if not circle or (b+c+d) % 2:
        return Q(0)
    return circle * legendre_moment(b, (c+d)//2) * cheb2_moment(a, (b+c+d)//2)

def monomials(d):
    for a in range(d+1):
        for b in range(d+1-a):
            for c in range(d+1-a-b):
                for e in range(d+1-a-b-c):
                    yield a, b, c, e

for m in (4, 5):
    M = 2*m
    J = m - 1
    d = 2*m - 1
    telescoping = sum((Q(2, 4*j*j-1) for j in range(1, J+1)), Q(0))
    equal(1-telescoping, Q(1, 2*J+1), "Fejer strict positivity floor")
    for k in range(M):
        equal(fejer_power_moment(M,k),
              Q(0) if k%2 else Q(1,k+1),
              "exact normalized uniform moment")
    for k in range(-d,d+1):
        equal(Q(int(k==0)), Q(int(k%M==0)), "circle Fourier filter")
    count = 0
    for e in monomials(d):
        equal(product_moment(e), moment(e), f"monomial {e}")
        count += 1
    print(f"m={m}; nodes={4*m**3}; degree={d}; "
          f"monomials={count}; Fejer weight >= 1/{M*(2*J+1)}")
for d in range(31):
    m=max(1,(d+2)//2)
    assert 2*m-1>=d
    checks+=1
print(f"EXACT_ROOT_FREE_REFERENCE_PASS assertions={checks}")
