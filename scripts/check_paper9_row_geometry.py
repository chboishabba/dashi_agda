#!/usr/bin/env python3
"""Finite exact parity of original Cauchy rows and chart permutations, not kernel proof."""
from fractions import Fraction as F
from itertools import product
from random import Random
from sympy import symbols, expand, __version__

a,b,c,u,v=symbols('a b c u v')
assert expand(a*b*c+(a*u+v)-(a*(b*c+u)+v))==0
print('recursive simplex regrouping polynomial PASS',flush=True)

def row(f,g,n): return sum(f[i]*g[n-i] for i in range(n+1))
def conv(f,g): return [row(f,g,n) for n in range(len(f))]
def add(f,g): return [a+b for a,b in zip(f,g)]
def scale(c,f): return [c*a for a in f]
def weight(q,f): return [q**i*a for i,a in enumerate(f)]
rng=Random(369)
N=33; unit=[F(1)]+[F(0)]*(N-1); zero=[F(0)]*N
checks=0
for _ in range(24):
    f,g,h=[[F(rng.randrange(-17,18),rng.randrange(1,10)) for i in range(N)] for j in range(3)]
    c=F(rng.randrange(-9,10),7)
    fg=conv(f,g)
    assertions=[(fg,conv(g,f)),(conv(fg,h),conv(f,conv(g,h))),
        (conv(add(f,g),h),add(conv(f,h),conv(g,h))),
        (conv(f,add(g,h)),add(fg,conv(f,h))),
        (conv(scale(c,f),g),scale(c,fg)),(conv(f,scale(c,g)),scale(c,fg)),
        (conv(unit,f),f),(conv(f,unit),f),(conv(zero,f),zero),
        (conv(weight(F(-1,7000),f),weight(F(-1,7000),g)),weight(F(-1,7000),fg)),
        (conv(weight(F(0),f),weight(F(0),g)),weight(F(0),fg))]
    for x,y in assertions:
        assert x==y; checks+=N
print(f'{checks} signed exact finite-row equalities (including q=0) PASS',flush=True)

def L(p): a,b,x,y=p;return a-b,b,x,x+y
def LB(p): a,b,x,y=p;return a+b,b,x,y-x
def R(p): a,b,x,y=p;return a,b-a,x+y,y
def RB(p): a,b,x,y=p;return a,a+b,x-y,y
def w(a,b): q=a*a-a*b+b*b;return q,q*q,q*q*q,a*a*b*b*(a-b)**2
npoints=0
for n in range(0,25):
    omega=[p for p in product(range(1,n+1),repeat=4) if p[0]*p[2]+p[1]*p[3]==n]
    assert len(omega)==len(set(omega));npoints+=len(omega)
    l=[p for p in omega if p[0]>p[1]]; r=[p for p in omega if p[1]>p[0]]
    lt=[p for p in omega if p[3]>p[2]]; rt=[p for p in omega if p[2]>p[3]]
    assert sorted(map(L,l))==sorted(lt) and sorted(map(R,r))==sorted(rt)
    assert sorted(map(LB,lt))==sorted(l) and sorted(map(RB,rt))==sorted(r)
    for k in range(4):
        lhs=sum(w(a+b,b)[k] for a,b,x,y in omega)+sum(w(a,b)[k] for a,b,x,y in omega if a==b)
        rhs=sum(w(a,b)[k] for a,b,x,y in omega)+sum(w(a+b,b)[k] for a,b,x,y in omega if x==y)
        assert lhs==rhs
print(f'25 actual box-filter grades (zero retained), {npoints} points, 100 signed boundary balances PASS')
print('SymPy',__version__)

# Finite original composition with zero constant term; retain signed q.
comp_checks=0
for N in range(1,17):
    inner=[F(0)]+[F(rng.randrange(-3,4),11) for _ in range(N-1)]
    outer=[F(rng.randrange(-7,8),13) for _ in range(N)]
    powers=[[F(1)]+[F(0)]*(N-1)]
    for k in range(1,N): powers.append(conv(inner,powers[-1]))
    assert all(powers[k][n]==0 for k in range(N) for n in range(k))
    comp=[sum(outer[k]*powers[k][n] for k in range(n+1)) for n in range(N)]
    for q in (F(0),F(-1,7),F(1,11)):
        for count in range(N+1):
            left=sum(q**n*comp[n] for n in range(count))
            right=sum(outer[k]*sum(q**n*powers[k][n] for n in range(count)) for k in range(count))
            assert left==right; comp_checks+=1
print(f'{comp_checks} weighted original finite composition prefix exchanges PASS')
