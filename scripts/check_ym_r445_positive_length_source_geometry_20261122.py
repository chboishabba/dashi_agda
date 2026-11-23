#!/usr/bin/env python3
"""Local exact original R445 geometry and conditional positive-correlation-length regression.

Actual full Wilson D1 common q and continuum OS gap are NOT inferred from geometry.
Reuses native R445 side-four positive links and original physical-cube SI geometry.
"""
from collections import Counter
from itertools import product
import sympy as s

def step(site,axis,k=1):
    p=list(site);p[axis]=(p[axis]+k)%4;return tuple(p)

fine={(mu,site) for mu in range(4) for site in product(range(4),repeat=4)}
assert len(fine)==1024
pairs=[]
for mu in range(4):
    for c in product(range(2),repeat=4):
        x=tuple(2*v for v in c)
        y=step(x,mu)
        pairs.append(((mu,x),(mu,y),step(y,mu)))
selected={b for x,y,_ in pairs for b in (x,y)}
assert len(pairs)==64 and len(selected)==128 and len(fine-selected)==896
assert all(len({x,y})==2 for x,y,_ in pairs)
# On the C4 cycle, +2 and -2 are opposite directed routes, both length 2a.
assert all(min((z[x[0]]-x[1][x[0]])%4,(x[1][x[0]]-z[x[0]])%4)==2
           for x,y,z in pairs)
occupancy=Counter()
for x in product(range(4),repeat=4):
    for mu in range(4):
        for nu in range(mu+1,4):
            plaq={(mu,x),(nu,x),(mu,step(x,nu)),(nu,step(x,mu))}
            occupancy[len(plaq&selected)]+=1
assert occupancy==Counter({0:1152,2:384})

for n in range(1,15):
    a=s.Rational(1,2**n)
    ai=1/a
    assert a>0 and ai>0 and a*ai==1 and 2*a>0
    assert (2*a)*(ai/2)==1

# Original full D1 permits q==0. qbar repairs the logarithm without
# changing the original bound: q^d <= qbar^d for every original Nat d.
for q in (s.Rational(0),s.Rational(1,10),s.Rational(1,2),s.Rational(99,100)):
    qb=(1+q)/2
    assert 0<qb<1 and q<=qb
    for d in range(150):
        assert q**d<=qb**d
    for a in (s.Rational(1,4),s.Rational(1,64)):
        L=2*a
        xi=L/(-s.log(qb))
        assert s.N(xi)>0
        assert s.simplify(s.exp(-L/xi)-qb)==0

r,xi=s.symbols('r xi',positive=True)
assert s.simplify(s.exp(-r/(-xi))-s.exp(r/xi))==0
assert s.limit(s.exp(r/xi),r,s.oo)==s.oo
assert all(abs((-s.Rational(1,2))**d)==s.Rational(1,2)**d
           for d in range(50))
a=s.symbols('a',positive=True)
assert s.limit((a**2)/a,a,0,dir='+')==0
assert s.limit(a/(a**2),a,0,dir='+')==s.oo

# BIPM exact defining SI values; hbar=h/(2*pi), c exact.
h=s.Rational(662607015,10**42)
c=s.Integer(299792458)
hbar=h/(2*s.pi)
mu=s.Rational(3,2)
assert hbar*mu/c != mu and s.N(hbar*mu/c)>0
Linv=(-1,0,0,0,0,0,0)
Hbar=(2,1,-1,0,0,0,0)
C=(1,0,-1,0,0,0,0)
add=lambda *v: tuple(sum(x[i] for x in v) for i in range(7))
neg=lambda v: tuple(-z for z in v)
assert add(Hbar,neg(C),Linv)==(0,1,0,0,0,0,0)
assert add(Hbar,C,Linv)==(2,1,-2,0,0,0,0)

print("PASS 64 native selected coarse pairs; 128 original fine bonds; 896 spectators")
print("PASS C4 positive two-step path length 2a; reverse path is not negative length")
print("PASS 384/1536 Wilson plaquettes touch two selected bonds")
print("PASS source positive spacing a>0 and reciprocal a*ainv=1 imply 2a>0")
print("PASS D1 qbar=(1+q)/2 always yields strictly positive finite envelope xi")
print("PASS xi<0 gives growing exponential, signed covariance does not imply xi<0")
print("PASS positive lattice gap a^2 has collapsing physical rate a and xi=1/a")
print("PASS SI hbar/c × m^-1 is kg, hbar*c × m^-1 is J, not naked magnitude equality")
print("OPEN full original real Wilson D1 q, all-cutoff marked support, E1/OS same-H gap")
