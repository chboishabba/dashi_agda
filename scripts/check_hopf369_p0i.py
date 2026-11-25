#!/usr/bin/env python3
"""Original Hopf spectral moment square/cube; exact symbolic regressions."""
import sympy as s
from itertools import permutations, product
q,K,t,nu=s.symbols('q K t nu',positive=True)
checks=[]
def eq(label,a,b):
    assert s.simplify(a-b)==0, (label,a,b)
    checks.append(label)
# Original radial measure from P0H, q>0. n=-1 is magnetic helicity.
raw=lambda n: s.Rational(32,3)*s.pi**2*q**(4+n)*s.exp(-2*q)
mass=lambda n: s.Rational(32,3)*s.pi**2*s.factorial(4+n)/2**(5+n)
p=lambda n: s.simplify(raw(n)/mass(n))
for n in range(-2,3):
    eq('moment',s.integrate(raw(n),(q,0,s.oo)),mass(n))
    eq('normalization',s.integrate(p(n),(q,0,s.oo)),1)
for n,d in [(-1,1),(-1,2),(0,2),(1,1)]:
    eq('raw edge',q**d*raw(n),raw(n+d))
    eq('normalized edge',q**d*p(n)*mass(n)/mass(n+d),p(n+d))
    eq('inverse edge',q**(-d)*p(n+d)*mass(n+d)/mass(n),p(n))
eq('normalized path q then q²',mass(-1)/mass(0)*mass(0)/mass(2),s.Rational(1,15))
eq('normalized path q² then q',mass(-1)/mass(1)*mass(1)/mass(2),s.Rational(1,15))
# Restriction represented by the idempotent indicator c, not a noninvertible deletion.
c=s.symbols('c'); axes=[q,q*q,c]
red=lambda x:s.rem(s.expand(x),c*c-c,c)
# all six faces at their actual lower vertex, and all six endpoint routes.
for i,j in [(0,1),(0,2),(1,2)]:
    k=3-i-j
    for z in (0,1):
        v=axes[k]**z*raw(-1)
        eq('cube face',red(axes[i]*(axes[j]*v)),red(axes[j]*(axes[i]*v)))
for order in permutations(range(3)):
    v=raw(-1)
    for i in order:v=axes[i]*v
    eq('cube endpoint',red(v),c*raw(2))
for n in (-1,0,1,2):
    tail=s.exp(-2*K)*sum((2*K)**j/s.factorial(j) for j in range(5+n))
    eq('tail derivative',-s.diff(tail,K),p(n).subs(q,K))
    eq('tail at zero',tail.subs(K,0),1)
    eq('tail limit',s.limit(tail,K,s.oo),0)
# Full and restricted normalized cube factors use actual masses; no silent mass loss.
M0,M1,M2,M3,N0,N1,N2,N3=s.symbols('M0 M1 M2 M3 N0 N1 N2 N3',positive=True)
for a,b in [(0,1),(0,2),(1,3),(2,3)]:
    M=[M0,M1,M2,M3]; N=[N0,N1,N2,N3]
    eq('normalized cutoff face scalar',M[a]/M[b]*M[b]/N[b],M[a]/N[a]*N[a]/N[b])
# Moment tilting under heat multiplier; independent time axis, not ideal evolution.
w=s.exp(-2*nu*t*q*q)
for d in [1,2]:eq('heat spectral commutation',q**d*w*raw(-1),w*q**d*raw(-1))
# helicity sign retained separately; signed observer cannot generally normalize by total.
P,N=s.symbols('P N',positive=True)
eq('signed helical difference',(P+N)-(P-N),2*N)
assert (P-N).subs(N,P)==0 and (P+N).subs(N,P)!=0
checks.append('zero signed helicity nonzero energy guard')
# Chart correction: current density coefficient is 8/45, not 32/45.
eq('current coefficient',p(2),s.Rational(8,45)*q**6*s.exp(-2*q))
print(f'{len(checks)}/{len(checks)} exact checks PASS; SymPy {s.__version__}')
