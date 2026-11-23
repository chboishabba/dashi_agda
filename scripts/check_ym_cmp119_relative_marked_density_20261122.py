#!/usr/bin/env python3
"""Exact rational two-source relative-density logarithmic Hessian tests.
Diagnostic only: not a physical Wilson RG activity estimate.
"""
from fractions import Fraction as Q
import sympy as s
u,v=s.symbols('u v')
def moments(law):
    assert sum((w for w,f,g in law),Q(0))==1
    return tuple(sum((w*f**i*g**j for w,f,g in law),Q(0)) for i,j in [(0,0),(1,0),(0,1),(1,1)])
def poly(m): return sum(s.Rational(x.numerator,x.denominator)*z for x,z in zip(m,[1,u,v,u*v]))
models=[[(Q(1,2),1,1),(Q(1,2),-1,-1)],[(Q(1,2),1,-1),(Q(1,2),-1,1)],[(Q(1,4),1,1),(Q(1,4),1,-1),(Q(1,4),-1,1),(Q(1,4),-1,-1)],[(Q(1,3),1,1),(Q(2,3),-1,1)]]
for x in models:
 for y in models:
  K=poly(moments(x)); T=poly(moments(y)); d=s.cancel((K-T)/T)
  exact=s.cancel(s.diff(s.log(K),u,v)-s.diff(s.log(T),u,v))
  proposed=s.cancel(s.diff(d,u,v)/(1+d)-s.diff(d,u)*s.diff(d,v)/(1+d)**2)
  assert s.cancel(exact-proposed)==0
  for a in [Q(-9,100),Q(0),Q(9,100)]:
   for b in [Q(-9,100),Q(0),Q(9,100)]:
    pt={u:s.Rational(a.numerator,a.denominator),v:s.Rational(b.numerator,b.denominator)}
    ds=abs(s.diff(d,u).subs(pt)); dt=abs(s.diff(d,v).subs(pt)); dst=abs(s.diff(d,u,v).subs(pt))
    assert 1+d.subs(pt)>0
    assert abs(exact.subs(pt)) <= dst/abs(1+d.subs(pt))+ds*dt/abs(1+d.subs(pt))**2
assert s.diff(u*v,u,v)==1 and (u*v).subs({u:0,v:0})==0
for law in models:
 M=poly(moments(law))
 for a in [Q(-9,100),Q(0),Q(9,100)]:
  for b in [Q(-9,100),Q(0),Q(9,100)]:
   z=M.subs({u:s.Rational(a),v:s.Rational(b)})
   assert z>0 and z >= s.Rational(91,100)**2 and z <= s.Rational(109,100)**2
print('PASS: 16 ordered pairs x 9 sources = 144 exact marked-density Hessian identities and bounds')
