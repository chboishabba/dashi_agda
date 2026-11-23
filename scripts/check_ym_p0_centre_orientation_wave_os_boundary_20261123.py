#!/usr/bin/env python3
"""Exact nine/ten centre sign wave and spectral non-promotion certificate.

Reuses the original balanced ternary nine sheet and five antipodal orbits.
The added fibre stiffness is *not* an original Wilson/OS coupling.
"""
from itertools import product
import sympy as sp

pts=list(product(range(3),repeat=2)); z=(0,0)
neg=lambda p:tuple((-a)%3 for a in p)
nz=[p for p in pts if p!=z]
axes={tuple(sorted((p,neg(p)))) for p in nz}
assert len(axes)==4 and len(nz)==8
cover=[(p,0) for p in nz]+[(z,1),(z,-1)]
inv=lambda item:(neg(item[0]),-item[1] if item[0]==z else 0)
assert len(cover)==10 and all(inv(inv(x))==x and inv(x)!=x for x in cover)
assert len({frozenset((x,inv(x))) for x in cover})==5
L=sp.zeros(9)
for i,p in enumerate(pts):
 for axis in range(2):
  for d in (-1,1):
   q=list(p);q[axis]=(q[axis]+d)%3
   L[i,i]+=1;L[i,pts.index(tuple(q))]-=1
assert L.eigenvals()=={sp.Integer(0):1,sp.Integer(3):4,sp.Integer(6):4}
dc=sp.ones(9,1);e=sp.eye(9)[:,pts.index(z)]
assert L*dc==sp.zeros(9,1) and L*e!=sp.zeros(9,1)
J=sp.zeros(10,9)
for i,(p,_) in enumerate(cover):J[i,pts.index(p)]=1
weight=sp.diag(*([1]*8+[sp.Rational(1,2)]*2))
P=J.T*weight;project=J*P
assert P*J==sp.eye(9) and project.rank()==9
b=sp.zeros(10,1);b[8]=1;b[9]=-1
assert P*b==sp.zeros(9,1) and (J*dc).T*weight*b==sp.zeros(1,1)
def H(k):
 h=J*L*P+k*(sp.eye(10)-project)
 assert P*h==L*P and h*J==J*L
 assert weight*h==h.T*weight
 return h
h0,h2=H(0),H(2)
assert h0.eigenvals()=={sp.Integer(0):2,sp.Integer(3):4,sp.Integer(6):4}
assert h2.eigenvals()=={sp.Integer(0):1,sp.Integer(2):1,sp.Integer(3):4,sp.Integer(6):4}
assert h0*b==sp.zeros(10,1) and h2*b==2*b
R=sp.zeros(10)
for i,x in enumerate(cover):R[cover.index(inv(x)),i]=1
assert R**2==sp.eye(10) and R*h0==h0*R and R*h2==h2*R
assert (sp.eye(10)+R).rank()==5 and (sp.eye(10)-R).rank()==5
assert R*b==-b and R*(J*dc)==J*dc

# Wave initial values are a *phase-space* pair, not just spatial amplitude.
# Equal displacement u0=0 with opposite nonzero velocity gives distinct futures.
t=sp.Rational(1,3);u=sp.zeros(9,1)
advance=lambda old,cur:2*cur-old-t*L*cur
energy=lambda old,cur:((cur-old).T*(cur-old))[0]/2+t*(cur.T*L*old)[0]/2
v=e
a=advance(u,v);c=advance(u,-v)
assert a==-c and a!=c
assert energy(u,v)==energy(v,a)==energy(u,-v)==energy(-v,c)==sp.Rational(1,2)
q=sp.eye(9)-dc*dc.T/9;v=q*e
assert dc.T*v==sp.zeros(1,1)
assert advance(u,v)==-advance(u,-v) and advance(u,v)!=advance(u,-v)
print("PASS 9 points/5 inversion orbits, 10 free-oriented states, double-labelled zero")
print("PASS exact 9-site Fourier DC distinct from source centre impulse")
print("PASS 9->10 pullback, conditional pushforward, residual rank 1, C2 parity 5+5")
print("PASS symmetric weighted wave lift: kappa0 double zero; kappa2 gap 2 INPUT")
print("PASS source discrete wave: opposite signed velocities, equal zero amplitudes, conserved energy")
print("PASS signed wave futures persist after exact DC-mode subtraction")
print("OPEN original SU(N) Wilson same-source OS/Hamiltonian physical identification")


# Original transfer-to-Hamiltonian issue: H(a)=-(1/a) log T(a).
# BOTH finite transfer gaps are strictly positive for integer n>=2,
# but their physical Hamiltonian energy limits are different.
n=sp.symbols('n',integer=True,positive=True)
transfer_vanish=1/n**2
transfer_survive=1/n
mass_vanish=-n*sp.log(1-transfer_vanish)
mass_survive=-n*sp.log(1-transfer_survive)
assert sp.limit(mass_vanish,n,sp.oo)==0
assert sp.limit(mass_survive,n,sp.oo)==1
assert sp.simplify(mass_vanish.subs(n,2))>0
assert sp.simplify(mass_survive.subs(n,2))>0
print('PASS positive finite transfer gaps 1/n^2 and 1/n: continuum masses 0 vs 1')
print('OPEN same original Wilson/OS transfer operator and physical scale-uniform bound')
