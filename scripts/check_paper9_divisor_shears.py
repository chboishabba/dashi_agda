#!/usr/bin/env python3
"""Exact checks of the divisor shear proof; not an Agda kernel replay."""
from fractions import Fraction as F
from sympy import symbols, expand, summation, Rational, __version__

a, b, x, y, d, t = symbols('a b x y d t', integer=True)
Q = a*a-a*b+b*b
weights = [Q, Q**2, Q**3, a*a*b*b*(a-b)**2]
diffs = [2*a*b, 4*(a**3*b+a*b**3), 6*(a**5*b+a*b**5)+14*a**3*b**3, 4*a**3*b**3]
scales = [6, 30, 420, 30]
boundaries = [5*d**3-6*d*d+d, 21*d**5-30*d**4+10*d**3-d,
              249*d**7-420*d**6+210*d**5-49*d**3+10*d, d**7-d**3]
diagonals = [a*a, a**4, a**6, 0]
assert expand((a-b)*x+b*(x+y)-(a*x+b*y)) == 0
assert expand(a*(x+y)+(b-a)*y-(a*x+b*y)) == 0
for f, diff, m, boundary, diag in zip(weights, diffs, scales, boundaries, diagonals):
    g = f.subs(a,a+b)
    assert expand(g-f.subs(b,a+b)) == 0
    assert expand(g-f-diff) == 0
    assert expand(f.subs(b,a)-diag) == 0
    h = expand(g.subs(b,d-a))
    G = expand(m*summation(h,(a,1,t)))
    assert G.subs(t,0) == 0
    assert expand(G.subs(t,t+1)-G-m*h.subs(a,t+1)) == 0
    assert expand(G.subs(t,d-1)-boundary) == 0
print('26 symbolic grade, weight, diagonal and boundary-antidifference identities PASS',flush=True)

def pairs(n):
    return [(a,n//a) for a in range(1,n+1) if n%a==0]
def sigma(n,k):
    return sum(a**k for a,_ in pairs(n))
def conv(n,k,l):
    return sum(sigma(i,k)*sigma(n-i,l) for i in range(1,n))
def left(p):
    a,b,x,y=p; return a-b,b,x,x+y
def leftback(p):
    a,b,x,y=p; return a+b,b,x,y-x
def right(p):
    a,b,x,y=p; return a,b-a,x+y,y
def rightback(p):
    a,b,x,y=p; return a,a+b,x-y,y

def W(a,b):
    q=a*a-a*b+b*b
    return q,q*q,q*q*q,a*a*b*b*(a-b)**2

points=0
for n in range(1,129):
    omega={(a,b,x,y) for i in range(1,n) for a,x in pairs(i) for b,y in pairs(n-i)}
    la={p for p in omega if p[0]>p[1]}; ly={p for p in omega if p[3]>p[2]}
    rb={p for p in omega if p[1]>p[0]}; rx={p for p in omega if p[2]>p[3]}
    assert {left(p) for p in la}==ly and {leftback(p) for p in ly}==la
    assert {right(p) for p in rb}==rx and {rightback(p) for p in rx}==rb
    assert all(leftback(left(p))==p for p in la)
    assert all(left(leftback(p))==p for p in ly)
    assert all(rightback(right(p))==p for p in rb)
    assert all(right(rightback(p))==p for p in rx)
    points+=len(omega)
    for k in range(4):
        assert sum(W(a+b,b)[k]-W(a,b)[k] for a,b,x,y in omega)==sum(W(a+b,b)[k] for a,b,x,y in omega if x==y)-sum(W(a,a)[k] for a,b,x,y in omega if a==b)
    s1,s3,s5,s7=(sigma(n,k) for k in (1,3,5,7))
    c11,c13,c15,c33=(conv(n,k,l) for k,l in ((1,1),(1,3),(1,5),(3,3)))
    assert 12*c11==5*s3+(1-6*n)*s1
    assert 240*c13==(10-30*n)*s3+21*s5-s1
    assert 120*c33==s7-s3
    assert 504*c15-2400*c33==(21-42*n)*s5+s1+20*s3
print(f'128 grades, {points} positive lattice points, both shear directions, 512 boundary identities and 512 divisor-convolution identities PASS',flush=True)
print('SymPy',__version__)
