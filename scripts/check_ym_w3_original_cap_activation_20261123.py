#!/usr/bin/env python3
"""Exact original 4D Wilson first cap-interaction source-jet diagnostic.

Activate gamma times ONE original marked cap plaquette in addition to
4d active original temporal wall plaquettes; all other couplings zero.
Imported compact Haar character convolution on this spherical two-cap
source gives Cov(F,G)=m_N'(gamma)*prod_wall m_N(beta_q).
This checks native 1536-face incidence and exact SU2 Haar Taylor
coefficients, not full 1536-coupling physics or Agda kernel acceptance.
"""
from collections import Counter
from itertools import combinations, product
import sympy as s

L=4
sites=tuple(product(range(L),repeat=4))
def step(x,a):
    y=list(x);y[a]=(y[a]+1)%L;return tuple(y)
def face(x,a,b):
    return ((x,a,1),(step(x,a),b,1),(step(x,b),a,-1),(x,b,-1))
faces={(x,a,b):face(x,a,b) for x in sites for a,b in combinations(range(4),2)}
assert len(sites)==256 and len(faces)==1536
F=((0,0,0,0),1,2)
def walls(d):
    return tuple(((t,dy,dz,0),0,a) for t in range(d) for a in (1,2)
                 for dy,dz in ([(0,0),(0,1)] if a==1 else [(0,0),(1,0)]))
def parity(surface):
    c=Counter((x,a) for p in surface for x,a,_ in faces[p])
    return {k for k,v in c.items() if v%2}

for d in (1,2):
    G=((d,0,0,0),1,2);T=walls(d)
    assert len(T)==4*d and not parity((F,G)+T)
    assert all(parity((F,G)+tuple(T[i] for i in range(4*d) if mask>>i&1))
               for mask in range((1<<(4*d))-1))
    assert F not in T and G not in T
    edges=Counter((x,a) for p in (F,G)+T for x,a,_ in faces[p])
    assert len(edges)==8*d+4 and all(n==2 for n in edges.values())
print('PASS native L4 1536 faces, d=1,2 cap spheres, all missing-wall subset obstructions')

b,g=s.symbols('b g',real=True)
def z(x):
    return sum(s.catalan(n)*x**(2*n)/(4**n*s.factorial(2*n))
               for n in range(9))
m=s.series(s.diff(z(b),b)/z(b),b,0,9).removeO().expand()
v=s.series(s.diff(z(g),g,2)/z(g)-
           (s.diff(z(g),g)/z(g))**2,g,0,8).removeO().expand()
assert s.simplify(m-(b/s.Integer(4)-b**3/96+b**5/1536-b**7/23040))==0
assert s.simplify(v-(s.Rational(1,4)-g**2/32+
                       5*g**4/1536-7*g**6/23040))==0
for d in (1,2):
    jet=s.expand(s.series(m**(4*d),b,0,4*d+3).removeO()*v)
    lead=jet.coeff(b,4*d)
    assert s.simplify(lead-v/s.Integer(4)**(4*d))==0
    assert lead.coeff(g,0)==s.Rational(1,4**(4*d+1))
    assert lead.coeff(g,2)==-s.Rational(1,32*4**(4*d))
    print('PASS original d=%s first coupled-wall cap source jet %s'%(d,lead))
assert v.subs(g,0)==s.Rational(1,4)
assert s.diff(v,g).subs(g,0)==0
assert s.diff(v,g,2).subs(g,0)==-s.Rational(1,16)
print('PASS exact SU2 Haar cap variance 1/4-gamma^2/32+5gamma^4/1536-7gamma^6/23040')
print('PASS counterexample to gamma-independent isolated-wall coefficient')
print('OPEN full homogeneous Wilson, CMP119 T and absolute CMP116 W3 charge shell')
