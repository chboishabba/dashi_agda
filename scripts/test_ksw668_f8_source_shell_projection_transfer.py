#!/usr/bin/env python3
"""Original KSW668 F8 effective-shell source and angular transfer controls.

Exact rational manufactured source/partition audit. These tests distinguish
- angular multiplication by a weighted source cell mass (commutes),
- original FV d=3+2ell conservative cell source, and
- ordinary 3D physical r^ell source averaging (does not generally
  commute with pointwise centre reconstruction).
Original physical compact bump and its primitive remain untouched in
scripts/ksw668_f8_fv_source_flux.py. No moving PDE/Agda acceptance claim.
"""
from fractions import Fraction as F
import random

ELL=(0,2,4)
D=(3,7,11)

def shell_volume(d,a,b):
    return (b**d-a**d)/d

def effective_cell_average(d,n,a,b):
    return shell_volume(d+n,a,b)/shell_volume(d,a,b)

def physical_cell_average(ell,n,a,b):
    return shell_volume(3+ell+n,a,b)/shell_volume(3,a,b)

rng=random.Random(66835)
checks=0
for ell,d in zip(ELL,D):
    for _ in range(18):
        cut=sorted(set([F(0),F(1)]+[F(rng.randrange(1,99),100) for _ in range(6)]))
        n=rng.choice([0,2,4])
        masses=[shell_volume(d+n,a,b) for a,b in zip(cut,cut[1:])]
        weights=[shell_volume(d,a,b) for a,b in zip(cut,cut[1:])]
        averages=[m/w for m,w in zip(masses,weights)]
        assert sum((w*v for w,v in zip(weights,averages)),F(0))==F(1,d+n)
        checks+=1

q=F(1,10) # Actual h/eps=0.008/0.04=1/5, first half-cell upper bound
for ell,d in zip(ELL,D):
    assert effective_cell_average(d,0,F(0),q)==1
    physical=physical_cell_average(ell,0,F(0),q)
    centre=F(0)**ell
    assert physical=={0:F(1),2:F(3,500),4:F(3,70000)}[ell]
    if ell: assert centre!=physical
    checks+=1

for ell in (2,4):
    for n in (0,2):
        assert physical_cell_average(ell,n,F(0),q)>0
        checks+=1

for ell,d in ((2,7),(4,11)):
    assert shell_volume(d,F(0),q)!=shell_volume(3+ell,F(0),q)
    checks+=1

# Original full TT angular tensor, exact 12-node rational circular rule;
# scalar multiplication commutes with its 12-node angular projection.
import sympy as s
x,r=s.symbols('x r',real=True)
from itertools import product
card=[(s.Integer(a),s.Integer(b)) for a,b in ((1,0),(-1,0),(0,1),(0,-1))]
diag=[(s.Rational(a,5),s.Rational(b,5)) for a,b in product((3,-3),(4,-4))]
diag += [(s.Rational(a,5),s.Rational(b,5)) for a,b in product((4,-4),(3,-3))]
nodes=[(a,b,s.Rational(527,4608)) for a,b in card]+[(a,b,s.Rational(625,9216)) for a,b in diag]
k=s.Matrix(s.symbols('kx ky kz'));P=k.dot(k)*s.eye(3)-k*k.T;Q=s.diag(0,1,-1)
T=(P*Q*P-P*s.trace(P*Q)/2).applyfunc(s.expand)
A=((x*x+r*r)**2+6*(x*x+r*r)*x*x+x**4)/8
for i,j,sign in ((1,1,1),(2,2,-1)):
    for mass in (F(-3,7),F(0),F(17,11)):
        mean=sum((w*T[i,j].subs({k[0]:x,k[1]:r*a,k[2]:r*b}) for a,b,w in nodes),s.S.Zero)
        assert s.expand(mean-sign*A)==0
        assert s.expand(s.Rational(mass.numerator,mass.denominator)*mean
            -sign*s.Rational(mass.numerator,mass.denominator)*A)==0
        checks+=1
print(f'{checks}/{checks} exact source-mass and tensor angular transport checks PASS')
print('First original physical shell q=h/(2eps)=1/10: ell2 3/500, ell4 3/70000, centre reconstruction zero.')
