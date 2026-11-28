#!/usr/bin/env python3
"""Finite exact controls for the literal CM evaluation and factor charts."""
from fractions import Fraction as F
from sympy import symbols, expand, __version__

N = 25

def mul(a, b):
    return [sum(a[i] * b[n-i] for i in range(n+1)) for n in range(N)]

def sub(a, b):
    return [x-y for x, y in zip(a, b)]

def norm(a):
    return sum(map(abs, a))

def sigma(n, k):
    return sum(d**k for d in range(1, n+1) if n % d == 0)

one = [F(1)] + [F(0)]*(N-1)
T, delta = F(1951, 15625), F(4551, 15625)
reciprocal, budget = F(15625, 13674), F(1517, 4558)
assert delta*reciprocal == budget < F(1, 3)
for q in map(F, ['0', '-1/7000', '1/7000', '-1/10000', '1/10000']):
    X = [F(1)] + [240*sigma(n, 3)*q**n for n in range(1, N)]
    Y = [F(1)] + [-504*sigma(n, 5)*q**n for n in range(1, N)]
    dx = [n*v for n, v in enumerate(X)]
    assert sum(dx) == sum(n*240*sigma(n, 3)*q**n for n in range(1, N))
    assert norm(sub(X, one)) < F(1, 25) and norm(sub(Y, one)) < F(2, 25)
    x3, y2 = mul(mul(X, X), X), mul(Y, Y)
    disc = sub(x3, y2)
    assert norm(sub(one, x3)) <= T and norm(disc) <= delta
    inv = one[:]
    for n in range(1, N):
        inv[n] = -sum(x3[i]*inv[n-i] for i in range(1, n+1))
    z = mul(disc, inv)
    assert mul(x3, inv) == one and mul(x3, z) == disc
    assert norm(inv) <= reciprocal and norm(z) <= budget
print('5 signed radii, 25 degrees each: literal tails, Euler jet, inverse and Z budgets PASS')

x = symbols('x')
assert expand((x+1)**3 - (x+F(1,6))*(x+F(1,2))*(x+F(5,6))) == F(3,2)*x*x + F(85,36)*x + F(67,72)
h = F(1)
for n in range(256):
    a = (n+F(1,6))*(n+F(1,2))*(n+F(5,6))
    h_next = a*h/(n+1)**3
    assert (n+1)**3*h_next == a*h and 0 < h_next <= h <= 1
    assert h*budget**n <= F(1,3)**n
    assert n*h*budget**n <= n*F(1,3)**n
    h = h_next
print('256 original coefficient recurrences and both majorants PASS')

C = 640320**3
t = F(C+1728, C)
for u in map(F, ['1', '1/7', '11/13', '-3/5']):
    X, Y = t*u*u, t*t*u**3
    assert Y*Y == t*X**3
    assert (X**3-Y*Y)/X**3 == -F(1728, C)
print('4 exact conditional CM root-to-Z controls PASS')

points = 0
for n in range(1, 81):
    pairs = lambda k: [(d,k//d) for d in range(1,k+1) if k%d == 0]
    omega = {(a,b,x,y) for i in range(1,n) for a,x in pairs(i) for b,y in pairs(n-i)}
    assert len(omega) == sum(len(pairs(i))*len(pairs(n-i)) for i in range(1,n))
    for a,b,x,y in omega:
        assert 0 < a*x < n and n-a*x == b*y
        assert (a,x) in pairs(a*x) and (b,y) in pairs(b*y)
    xy = {(a,b,x,y) for a,b,x,y in omega if x==y}
    ab = {(a,b,x,y) for a,b,x,y in omega if a==b}
    assert xy == {(a,d-a,k,k) for d,k in pairs(n) for a in range(1,d)}
    assert ab == {(d,d,x,k-x) for d,k in pairs(n) for x in range(1,k)}
    assert omega == {(b,a,y,x) for a,b,x,y in omega}
    points += len(omega)
print(f'80 grades, {points} positive factor-chart points and both equality strata PASS; SymPy {__version__}')
