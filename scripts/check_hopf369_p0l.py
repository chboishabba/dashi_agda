#!/usr/bin/env python3
"""Exact finite observer cube and original biological causal face replay."""
from itertools import product, permutations
import sympy as s
checks=0
def ck(p):
    global checks
    assert p
    checks+=1
# Source coefficient (complex vector), signed eigenvalue, observer weight,
# and selection flag remain separate. Zero carries no inverse-curl observer.
def advance(a):
    l,source,w,keep=a
    return (l,source,l*w if l else None,keep)
def double(a):return advance(advance(a))
def split(a):return (a[3],a)
def lift(f):return lambda a:(a[0],f(a[1]))
for lam,phase,keep in product((-3,-2,-1,0,1,2,3),(1,-1,s.I,-s.I),(False,True)):
    source=(phase,phase*s.I,0)
    a=(lam,source,s.Rational(2,lam) if lam else None,keep if lam else True)
    b,c,d=advance(a),double(a),advance(double(a))
    ck(double(b)==advance(c))
    ck(split(b)==lift(advance)(split(a)))
    ck(split(c)==lift(double)(split(a)))
    ck(lift(double)(split(b))==lift(advance)(split(c)))
    ck(split(d)==lift(advance)(split(c)))
    ck(split(d)==lift(double)(split(b)))
    for order in permutations('xyz'):
        v=a;cut=False
        for axis in order:
            if axis=='z':v=split(v);cut=True
            else:
                f=advance if axis=='x' else double
                v=lift(f)(v) if cut else f(v)
        ck(v==split(d))
    ck(split(a)[1]==a)
    ck(d[1]==source)
    ck(d[2]==(2*lam**2 if lam else None))
# The exact original tissue fixture, not a physical PNP calibration.
def signal(a):g,c,h,j,e,p=a;return g,c,h,j,e,g and h and j and e
def restore(a):g,c,h,j,e,p=a;return g,c,1,j,e,p
def project(a):return a[:1]+a[2:]
def cs(a):g,h,j,e,p=a;return g,h,j,e,g and h and j and e
def cr(a):g,h,j,e,p=a;return g,1,j,e,p
counts={-1:0,0:0,1:0}
for a in product((0,1),repeat=6):
    x,y=signal(a),restore(a);l,r=restore(x),signal(y)
    cl,crr=cr(cs(project(a))),cs(cr(project(a)))
    for f,g,v in [(signal,cs,a),(restore,cr,a),(signal,cs,y),(restore,cr,x)]:ck(project(f(v))==g(project(v)))
    ck(project(l)==cl);ck(project(r)==crr)
    delta=r[-1]-l[-1];ck(delta==crr[-1]-cl[-1]);counts[delta]+=1
    ck(delta==a[0]*(1-a[2])*a[3]*a[4])
ck(counts=={-1:0,0:60,1:4})
# Curved Hodge: B is a flat vector, beta_g = f B (one-form), f=psi^-2.
x,y,z=s.symbols('x y z',real=True);X=(x,y,z);D=1+x*x+y*y+z*z
B=8*s.Matrix([2*x*z-2*y,2*x+2*y*z,1-x*x-y*y+z*z])/D**3
f=s.Function('f')(*X)
def curl(v):return s.Matrix([s.diff(v[2],y)-s.diff(v[1],z),s.diff(v[0],z)-s.diff(v[2],x),s.diff(v[1],x)-s.diff(v[0],y)])
grad=s.Matrix([s.diff(f,t) for t in X]);J=curl(B)
res=f*curl(f*B)-f*f*J-f*grad.cross(B)
for v in res:ck(s.factor(v)==0)
# Use a positive nonconstant conformal fixture psi=1+1/D, not the P0H fixed point.
point={x:1,y:0,z:0};fv=D**2/(D+1)**2
rv=(fv*s.Matrix([s.diff(fv,t) for t in X]).cross(B)).subs(point)
ck(rv!=s.zeros(3,1));print('curved residual at (1,0,0):',rv.T)
print('causal signed residual counts:',counts)
print(f'{checks}/{checks} exact checks PASS; SymPy {s.__version__}')
