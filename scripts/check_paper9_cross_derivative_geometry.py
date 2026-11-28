#!/usr/bin/env python3
"""Independent exact geometry regression; not native kernel verification."""
from fractions import Fraction as F
from random import Random
import sympy as S

Z = (F(0), F(0))
I = (F(1), F(0))

def add(a, b): return a[0]+b[0], a[1]+b[1]
def neg(a): return -a[0], -a[1]
def sub(a, b): return add(a, neg(b))
def mul(a, b): return a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]
def real(a): return F(a), F(0)
def div(a, b):
    d = b[0]*b[0]+b[1]*b[1]
    return mul(a, (b[0]/d, -b[1]/d))
def power(a, n):
    r = I
    for _ in range(n): r = mul(r, a)
    return r
def prod(xs):
    r = I
    for a in xs: r = mul(r, a)
    return r
def rest(cs, x): return prod(add(c, x) for c in cs)
def slope(cs, x):
    r, t = I, Z
    for c in reversed(cs):
        t, r = add(r, mul(c, t)), mul(add(c, x), r)
    return t
def horner(cs, x):
    r = Z
    for c in cs: r = add(mul(x, r), c)
    return r
def asc(cs, x): return horner(reversed(cs), x)
def shift(cs, k):
    a = []
    for c in cs:
        a = [add(c, mul(k, a[0]))] + [add(a[i-1], mul(k, a[i])) for i in range(1, len(a))] + [a[-1]] if a else [c]
    return a
def wing(u, v, n):
    q = Z
    for k in range(n): q = add(q, mul(power(u, k), power(v, n-1-k)))
    return q

def main():
    rng = Random(163)
    def c(d=5): return F(rng.randint(-7, 7), d), F(rng.randint(-7, 7), d)
    counts = dict(shift=0, cross=0, slope=0, wings=0, derivative=0, moment=0, symbolic=0)
    for d in (1, 2, 3, 10, 42, 82):
        for _ in range(4):
            cs, k, x = [c() for j in range(d+1)], c(), c()
            assert asc(shift(cs, k), x) == horner(cs, add(k, x))
            counts['shift'] += 1
    for _ in range(40):
        cs = [c() for _ in range(40)]
        w, X, xp, xm = c(), c(), c(), c()
        if w == Z: w = I
        if X == Z: X = I
        x, plus, minus = mul(w, X), mul(w, xp), mul(w, xm)
        n, m = mul(plus, minus), mul(sub(x, plus), sub(x, minus))
        r0, r1, t = rest(cs, Z), rest(cs, x), slope(cs, x)
        assert sub(r1, r0) == mul(x, t)
        p, s = div(mul(m, r1), power(x, 2)), div(mul(n, r0), power(x, 2))
        assert mul(sub(mul(n, p), mul(m, s)), power(x, 2)) == mul(mul(n, m), mul(x, t))
        N, M = mul(xp, xm), mul(sub(X, xp), sub(X, xm))
        assert mul(sub(mul(N, p), mul(M, s)), power(X, 2)) == mul(mul(N, M), mul(X, mul(w, t)))
        counts['cross'] += 2
        assert slope(cs, Z) == sum_pairs(prod(cs[:i]+cs[i+1:]) for i in range(40))
        counts['slope'] += 2
    for _ in range(60):
        u, v = c(12), c(12)
        n = rng.randrange(0, 24)
        assert sum(t*t for t in u) <= 1 and sum(t*t for t in v) <= 1
        q = wing(u, v, n)
        assert sub(power(v, n), power(u, n)) == mul(sub(v, u), q)
        assert max(map(abs, q)) <= 2*n
        assert wing(u, u, n) == (mul(real(n), power(u, n-1)) if n else Z)
        counts['wings'] += 3
        f = [c() for _ in range(12)]
        d = sum_pairs(mul(a, wing(u, v, i)) for i, a in enumerate(f))
        assert sub(asc(f, v), asc(f, u)) == mul(sub(v, u), d)
        center = sum_pairs(mul(a, wing(u, u, i)) for i, a in enumerate(f))
        assert center == asc([mul(real(i), a) for i, a in enumerate(f) if i], u)
        counts['derivative'] += 2
        s = F(3, 4)
        a = c()
        b = mul(a, real(s**n))
        assert 2*n*sum(map(abs, b)) <= 4*sum(map(abs, a))/(1-s)**2
        counts['moment'] += 1
    a,b,s,t,u,v,w,alpha = S.symbols('a b s t u v w alpha')
    beta = -S.Rational(81,41)-alpha
    rel = alpha**2+S.Rational(81,41)*alpha+1
    c0,m0 = S.Rational(163,41), S.Rational(163,1681)
    X = a+b*w
    Xp = alpha*a+alpha**2*b*w
    Xm = beta*a+beta**2*b*w
    N = S.Poly(S.expand(Xp*Xm), w)
    M = S.Poly(S.expand((X-Xp)*(X-Xm)), w)
    for got, want in ((N.nth(0),a*a),(N.nth(1),-S.Rational(81,41)*a*b),(M.nth(0),c0*a*a),(M.nth(1),m0*a*b)):
        assert S.rem(S.expand(got-want),rel,alpha)==0
        counts['symbolic'] += 1
    P = u+v*w*a
    Q = s+t*w*a
    lhs = (Xp*Xm*P-(X-Xp)*(X-Xm)*Q)*X**2
    rhs = Xp*Xm*(X-Xp)*(X-Xm)*X*w*t
    got = S.rem(S.expand(lhs-rhs).coeff(w,1), rel, alpha)
    literal = ((-S.Rational(81,41)*a*b*u+a*a*v*a-(m0*a*b*s+c0*a*a*t*a))*a*a+(a*a*u-c0*a*a*s)*2*a*b-a*a*c0*a*a*a*t)
    assert S.expand(got-literal)==0
    counts['symbolic'] += 1
    kap = -S.Rational(77859659565707,19943834790540897829879824384000)
    assert S.expand(literal.subs({u:c0*s,v:2*c0*t+c0*kap*s})-c0*a**3*s*(kap*a*a-2*b))==0
    counts['symbolic'] += 1
    print('PASS', sum(counts.values()), counts)

def sum_pairs(xs):
    r = Z
    for a in xs: r = add(r, a)
    return r

if __name__ == '__main__': main()
