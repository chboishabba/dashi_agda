#!/usr/bin/env python3
"""Exact finite regressions for Paper 9 second wings and relaxed disk reduction.

Not a Bishop/Lean kernel run, analytic convergence, or modular invariance proof.
"""
from fractions import Fraction as F
from math import comb
import random
import sympy as s


def q(u, v, n):
    a = 0
    for k in range(n):
        a = v**k + u*a
    return a


def t(u, v, w, n):
    a = 0
    for k in range(n):
        a = q(v, w, k) + u*a
    return a


def reduce(x, y):
    """Exact rational model of the overlapping constructive S/T chart."""
    assert y > 0
    steps = 0
    a, b, c, d = 1, 0, 0, 1
    X, Y = x, y
    while Y < F(1, 2):
        # In Bishop, approximate X within 1/10, then round that approximation.
        k = (X + F(1, 2)) // 1
        X -= k
        a, b = a-k*c, b-k*d
        assert abs(X) <= F(3, 5) and Y <= F(3, 5)
        norm = X*X + Y*Y
        assert 0 < norm <= F(18, 25)
        old = Y
        X, Y = -X/norm, Y/norm
        a, b, c, d = -c, -d, a, b
        assert Y >= F(25, 18)*old
        steps += 1
        assert steps < 1000
    den = (c*x+d)**2 + (c*y)**2
    assert a*d-b*c == 1
    assert Y == y/den
    assert X == ((a*x+b)*(c*x+d)+a*c*y*y)/den
    return steps


def main():
    rng = random.Random(16341)
    u, v, w = s.symbols("u v w")
    counts = dict(symbolic=0, rational=0, reduction=0, poisson=0, euler=0)
    for n in range(13):
        assert s.expand(q(u,w,n)-q(u,v,n)-(w-v)*t(u,v,w,n)) == 0
        assert s.expand(t(u,v,w,n)-sum(u**i*v**j*w**(n-2-i-j)
            for i in range(n-1) for j in range(n-1-i))) == 0
        assert s.expand(t(u,u,u,n)-(comb(n,2)*u**(n-2) if n>=2 else 0)) == 0
        counts["symbolic"] += 3
    for _ in range(180):
        a,b,c = [F(rng.randint(-9,9),10) for _ in range(3)]
        n = rng.randrange(32)
        assert q(a,c,n)-q(a,b,n) == (c-b)*t(a,b,c,n)
        assert abs(t(a,b,c,n)) <= comb(n,2)
        counts["rational"] += 2
    for _ in range(800):
        x = F(rng.randint(-100000,100000),rng.randint(1,100))
        y = F(rng.randint(1,100),rng.randint(1,100000))
        reduce(x,y)
        counts["reduction"] += 1
    # Positive Poisson gap: (R^2-|z|^2)/|R*e^{it}-z|^2
    # >= (R-r)/(R+r). Rational circle parametrization; test exact.
    R, r = F(3,4), F(1,4)
    for _ in range(300):
        h = F(rng.randint(-100,100),rng.randint(1,100))
        c, d = (1-h*h)/(1+h*h), 2*h/(1+h*h)
        x,y = F(rng.randint(-10,10),100), F(rng.randint(-10,10),100)
        assert x*x+y*y <= r*r
        den = (R*c-x)**2+(R*d-y)**2
        assert den > 0
        assert (R*R-x*x-y*y)*(R+r) >= (R-r)*den
        counts["poisson"] += 1
    # Disk phase q(w)=q0 exp(-2p*w/(1-w)); each monomial has
    # Euler first/second multipliers n,n^2. No floating point.
    p = s.symbols("p")
    for n in range(30):
        e = 1-2*p*n*w+(-2*p*n+2*p*p*n*n)*w*w
        actual = s.series(s.exp(-2*p*n*w/(1-w)),w,0,3).removeO()
        assert s.expand(actual-e) == 0
        counts["euler"] += 1
    print(counts, "total", sum(counts.values()), "PASS")


if __name__ == "__main__":
    main()
