#!/usr/bin/env python3
"""P0J: original Hopf spectral observer fibres and finite control discriminators."""
import sympy as s
from itertools import product
checks=[]
def eq(label,a,b):
    assert s.simplify(a-b)==0,(label,a,b)
    checks.append(label)
x,y,z,a,q,K=s.symbols('x y z a q K',real=True)
D=1+x*x+y*y+z*z
B=8*s.Matrix([2*x*z-2*y,2*x+2*y*z,1-x*x-y*y+z*z])/D**3
A=D*B/4
Bshift=B.subs(z,z-a)
Ashift=A.subs(z,z-a)
for name,v,w in [('energy',B,B),('helicity',A,B)]:
    eq('translated local '+name,v.subs(z,z-a).dot(w.subs(z,z-a)),v.dot(w).subs(z,z-a))
eq('original receiver Bz',B[2].subs({x:0,y:0,z:0}),8)
eq('translated receiver Bz',Bshift[2].subs({x:0,y:0,z:0}),8/(1+a*a)**2)
eq('translated receiver energy',Bshift.dot(Bshift).subs({x:0,y:0,z:0}),64/(1+a*a)**4)
assert Bshift[2].subs({x:0,y:0,z:0,a:1})!=B[2].subs({x:0,y:0,z:0});checks.append('same spectrum different receiver guard')
eq('translation phase unit modulus',s.exp(-s.I*q*a)*s.exp(s.I*q*a),1)
for n in range(-2,3):
    m=s.Rational(32,3)*s.pi**2*q**(4+n)*s.exp(-2*q)
    eq('all spectral moments invariant under translation',m*s.exp(-s.I*q*a)*s.exp(s.I*q*a),m)
eq('field reversal energy',(-B).dot(-B),B.dot(B))
eq('field reversal helicity',(-A).dot(-B),A.dot(B))
assert (-B[2]).subs({x:0,y:0,z:0})!=B[2].subs({x:0,y:0,z:0});checks.append('signed local response guard')
# Pointwise tail bound for inverse Fourier reconstruction; all integer derivative orders.
for d in range(5):
    t=s.factorial(3+d)*s.exp(-K)*sum(K**j/s.factorial(j) for j in range(4+d))
    eq('phase retaining tail derivative',-s.diff(t,K),K**(3+d)*s.exp(-K))
    eq('phase retaining tail total',t.subs(K,0),s.factorial(3+d))
# Existing Sheldrake two-stage binomial toy: normalized exponential reweighting.
p,r,u=s.symbols('p r u',positive=True)
P=s.Matrix([(1-p)**2,2*p*(1-p),p*p]);w=lambda a:s.diag(1,a,a*a)
def norm(v):return v/sum(v)
for i in range(3):
    eq('Galton tilt composition',norm(w(u)*norm(w(r)*P))[i],norm(w(r*u)*P)[i])
    pp=r*p/(1-p+r*p)
    eq('Galton binomial closure',norm(w(r)*P)[i],s.Matrix([(1-pp)**2,2*pp*(1-pp),pp**2])[i])
# Replay literal six-Boolean biological fixture (not a fresh biology law).
acts=range(5)
def step(a,x):
    g,c,h,j,e,p=x
    if a==0:p=g and h and j and e
    if a==1:p=0
    if a==2:j=1
    if a==3:h=1
    if a==4:e=1
    return g,c,h,j,e,p
def proj(x):return x[:1]+x[2:]
def coarse(a,x):
    g,h,j,e,p=x
    if a==0:p=g and h and j and e
    if a==1:p=0
    if a==2:j=1
    if a==3:h=1
    if a==4:e=1
    return g,h,j,e,p
for v in product((0,1),repeat=6):
    for act in acts:
        assert proj(step(act,v))==coarse(act,proj(v));checks.append('original fixture projection')
v=(1,0,0,1,1,0);w0=(1,0,1,1,1,0)
assert v[-1]==w0[-1] and step(0,v)[-1]!=step(0,w0)[-1];checks.append('morphology only fails future control')
print(f'{len(checks)}/{len(checks)} exact checks PASS; SymPy {s.__version__}')
