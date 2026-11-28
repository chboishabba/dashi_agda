#!/usr/bin/env python3
"""Raw signed coordinate regression, not universal proof reflection."""
from fractions import Fraction as F
from math import isqrt
from random import Random

A, B, C = 13591409, 545140134, 640320**3


def add(p, q):
    a, b = p
    c, d = q
    return a*d+c*b, b*d


def le(p, q):
    a, b = p
    c, d = q
    assert b > 0 and d > 0
    return a*d <= c*b


def term(k):
    a = (2*k+1)*5**(2*k+1)
    b = (2*k+1)*239**(2*k+1)
    return (-1)**k*(16*b-4*a), a*b


def raw_prefixes(count):
    p, q, t = 1, 1, 0
    out = [(0, 1)]
    for j in range(count):
        a, b = (1, 1) if j == 0 else (-24*(2*j-1)*(6*j-5)*(6*j-1), C*j**3)
        p *= a
        q *= b
        t = t*b+p*(A+B*j)
        out.append((t, q))
    return out


def window(k, prefixes):
    n, s = 1+(k+4)//41, 2**(k+2)
    target = 10005*s*s
    r = isqrt(target)
    assert r*r <= target < (r+1)**2
    x, y = prefixes[n:n+2]
    lo, hi = (x, y) if le(x, y) else (y, x)
    return (426880*r*hi[1], s*hi[0]), (426880*(r+1)*lo[1], s*lo[0])


def main():
    import sympy as S
    x = S.symbols('x')
    gap = C*(x+1)**3*(A+B*x)-2**41*24*(2*x+1)*(6*x+1)*(6*x+5)*(A+B*(x+1))
    assert S.Poly(gap,x).all_coeffs() == [141048195668958693853495296,427696936518221473282523136,435555656263180381923311616,152324142589183949932855296,3420813714202353688903680]
    # Exact zero-stage Machin upper bound from 3 and 2 terms.
    atan = lambda d, n: sum((F((-1)**j,(2*j+1)*d**(2*j+1)) for j in range(n)), F(0))
    assert 16*atan(5,3)-4*atan(239,2) < F(22,7)
    p = raw_prefixes(20)
    m, mval = (0,1), F(0)
    for k in range(129):
        l, u = window(k,p)
        e = (22,7) if k == 0 else (4,25**k)
        assert F(*m) == mval
        assert le(l,add(m,e)) and le(m,add(u,e))
        ln,ld = l; un,ud = u; mn,md = m; en,ed = e
        assert ln*md*ed <= (mn*ed+en*md)*ld
        assert mn*ud*ed <= (un*ed+en*ud)*md
        n, s = 1+(k+4)//41, 2**(k+2)
        lo,hi = sorted(map(lambda q:F(*q),p[n:n+2]))
        r = isqrt(10005*s*s)
        assert F(*l)==F(426880*r,s)/hi and F(*u)==F(426880*(r+1),s)/lo
        assert F(*l)<=mval+F(*e) and mval<=F(*u)+F(*e)
        m = add(m,term(k))
        mval += F((-1)**k,2*k+1)*(F(16,5**(2*k+1))-F(4,239**(2*k+1)))
    rng = Random(369)
    for _ in range(1000):
        a,b,c,d = rng.randrange(-100,101),rng.randrange(1,101),rng.randrange(-100,101),rng.randrange(1,101)
        assert le((a,b),(c,d)) == (F(a,b)<=F(c,d))
        assert F(*add((a,b),(c,d)))==F(a,b)+F(c,d)
    assert not le((1,1),(0,1)) and le((-1,1),(0,1))
    assert le((0,1),(0,99)) and le((1,2),(2,4))
    for t in range(1000):
        r=isqrt(t)
        assert r*r<=t<(r+1)**2
        assert sum(j*j<=t<(j+1)**2 for j in range(r+2))==1
    print('PASS: 5 gap coefficients, stage-zero bound, 129 raw source stages and both signed comparisons, 1000 signed order/add cases, 1000 strict-floor uniqueness cases, sign and equality controls')

if __name__ == '__main__':
    main()
