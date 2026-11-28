"""Exact coordinate/gauge regression, not a PDE existence or kernel proof."""
from fractions import Fraction as Q
from itertools import product
import sympy as s

checks=0
def ck(ok):
    global checks
    if not ok: raise AssertionError('signed coordinate guard failed')
    checks+=1

# Original xi argument: s=(1/2-Im t)+i Re t; inverse keeps the sign.
for a,b in product(map(Q,(-2,-1,0,1,2)),repeat=2):
    for d in (Q(1),Q(3),Q(7)):
        r,i=a/d,b/d
        u,v=i,Q(1,2)-r
        ck((Q(1,2)-v,u)==(r,i))
        ck(v==-(r-Q(1,2)))

# Nonconstant moving frame, test the exact PDE residual identity without
# assuming the sample velocity solves NS. Polynomial controls retain signs.
t,x,y,z=s.symbols('t x y z'); X=s.Matrix([x,y,z]); nu=s.symbols('nu')
u0=s.Matrix([t*x+y*z,x*z+t*y,x*y+t*z]); p=t*x*y+z*z+t*t*z
for b in (s.Matrix([t**2,2*t**3,-t**2]),s.Matrix([t**3,-t**2,t**4]),s.zeros(3,1)):
    shift=dict(zip(X,X+b)); bt=b.diff(t); btt=bt.diff(t)
    U=u0.subs(shift,simultaneous=True); V=U-bt
    pressure=p.subs(shift,simultaneous=True)+(btt.T*X)[0]
    def lap(w):return w.applyfunc(lambda v:sum(s.diff(v,q,2) for q in X))
    def grad(p):return s.Matrix([s.diff(p,q) for q in X])
    def residual(w,p):return w.diff(t)+w.jacobian(X)*w-nu*lap(w)+grad(p)
    ck(all(s.expand(e)==0 for e in residual(V,pressure)-residual(u0,p).subs(shift,simultaneous=True)))
    ck(s.expand(s.trace(V.jacobian(X))-s.trace(u0.jacobian(X)).subs(shift,simultaneous=True))==0)
    ck(V.subs(t,0)==u0.subs(t,0))
# Periodic gradient with time-dependent affine monodromy; cancel the
# actual increments by b''=-c. This is not a PDE-solution fixture.
c=s.Matrix([t,2*t*t,-3*t]); b=s.Matrix([-t**3/6,-t**4/6,t**3/2]); pp=sum(s.sin(2*s.pi*q) for q in X)+(c.T*X)[0]
ck(b.diff(t,2)==-c)
shift=dict(zip(X,X+b)); gauge=pp.subs(shift,simultaneous=True)+(b.diff(t,2).T*X)[0]
for i in range(3):ck(s.simplify(gauge.subs(X[i],X[i]+1)-gauge)==0)
print(f'{checks}/{checks} signed coordinate/gauge controls PASS')
