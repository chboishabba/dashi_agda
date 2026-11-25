#!/usr/bin/env python3
"""Exact BPST charts, Hopf flux surface, compact/periodic MHD and moving Maxwell.
Classical geometry and conditional source realization, not device validation.
"""
import sympy as s
from itertools import combinations
X=s.symbols('x y z',real=True); x,y,z=X
w=s.symbols('w0:4',real=True); a,b,c,d=w
rho=s.symbols('rho',positive=True); R2=sum(i*i for i in w)
V=s.Matrix([b,c,d]); zero=s.zeros(3,1)
checks=[]
def clean(v):return v.applyfunc(lambda a:s.factor(s.together(a))) if isinstance(v,s.MatrixBase) else s.factor(s.together(v))
def eq(name,a,b):
    d=clean(a-b)
    assert d==(s.zeros(*d.shape) if isinstance(d,s.MatrixBase) else 0),name
    checks.append(name); print(name,flush=True)
def grad(f):return s.Matrix([s.diff(f,i) for i in X])
def div(v):return clean(sum(s.diff(v[i],X[i]) for i in range(3)))
def curl(v):return clean(s.Matrix([s.diff(v[2],y)-s.diff(v[1],z),s.diff(v[0],z)-s.diff(v[2],x),s.diff(v[1],x)-s.diff(v[0],y)]))
# q=w/|w|. N=Im(dw conjugate(w)), M=Im(conjugate(w)dw).
N=[a*V.diff(i)-s.diff(a,i)*V+V.cross(V.diff(i)) for i in w]
M=[a*V.diff(i)-s.diff(a,i)*V-V.cross(V.diff(i)) for i in w]
C=[-n/(R2+rho*rho) for n in N]
Cp=[rho*rho*m/(R2*(R2+rho*rho)) for m in M]
def adj(v):return clean(((a*a-V.dot(V))*v+2*V*V.dot(v)-2*a*V.cross(v))/R2)
for i in range(4):eq('gauge transition',adj(C[i])+M[i]/R2,Cp[i])
def curvature(A,i,j):return clean(A[j].diff(w[i])-A[i].diff(w[j])+2*A[i].cross(A[j]))
F={(i,j):curvature(C,i,j) for i,j in combinations(range(4),2)}
for i,j in F:eq('curvature covariance',curvature(Cp,i,j),adj(F[i,j]))
for i,j,k,l,sgn in [(0,1,2,3,1),(0,2,1,3,-1),(0,3,1,2,1)]:eq('self-duality',F[i,j],sgn*F[k,l])
# Standard generators e_i/2, F^a=2 times imaginary-quaternion components.
eq('BPST component norm',8*sum(v.dot(v) for v in F.values()),192*rho**4/(R2+rho*rho)**4)
# inversion y=w/|w|²: pull Cp back by w=y/|y|², gives smooth M(y)*rho²/(1+rho²|y|²).
Y=s.symbols('Y0:4',real=True); Y2=sum(i*i for i in Y); yv=s.Matrix(Y[1:]); inv=s.Matrix(Y)/Y2
for i in range(4):
    pull=clean(sum((Cp[j].subs(dict(zip(w,inv)),simultaneous=True)*s.diff(inv[j],Y[i]) for j in range(4)),zero))
    target=rho*rho*(Y[0]*yv.diff(Y[i])-s.diff(Y[0],Y[i])*yv-yv.cross(yv.diff(Y[i])))/(1+rho*rho*Y2)
    eq('infinity smooth chart',pull,target)
# Original Euclidean Hopf field, t is a global smooth flux function.
D=1+x*x+y*y+z*z
A=2*s.Matrix([2*x*z-2*y,2*x+2*y*z,1-x*x-y*y+z*z])/D**2
B=curl(A); t=4*(x*x+y*y)/D**2
eq('original field',B,4*A/D);eq('solenoidal',div(B),0);eq('flux function',B.dot(grad(t)),0)
# Generic smooth cutoff, using chain rule instead of a sampled polynomial.
h,hp=s.symbols('h hp',real=True); H=h*B; dh=hp*grad(t)
eq('cutoff divergence',h*div(B)+dh.dot(B),0)
J=clean(h*curl(B)+dh.cross(B)); pgrad=clean(-h*dh*B.dot(B)-h*h*grad(B.dot(B))/2)
for sign in (-1,1):
    u=sign*H; adv=clean(h*h*B.jacobian(X)*B+h*B*dh.dot(B))
    eq('compact MHD force',adv+pgrad,J.cross(H))
    eq('compact E',-u.cross(H),zero)
    eq('compact momentum flux',u*u.T-H*H.T,s.zeros(3))
# Translation comparator: prescribed source in c=mu=epsilon=1 units.
v=s.symbols('v',real=True); vel=s.Matrix([0,0,v]); E=-vel.cross(B)
def dt(a):return clean(-v*a.diff(z))
charge=div(E); current=clean(curl(B)-dt(E)); S=clean(E.cross(B)); U=clean((E.dot(E)+B.dot(B))/2)
eq('Faraday',dt(B)+curl(E),zero)
eq('Ampere',curl(B)-dt(E),current)
eq('charge continuity',dt(charge)+div(current),0)
eq('Poynting balance',dt(U)+div(S)+current.dot(E),0)
eq('Gauss magnetic',div(B),0)
# Maxwell momentum density S and momentum-flux tensor (negative Maxwell stress).
Pi=U*s.eye(3)-E*E.T-B*B.T
force=clean(charge*E+current.cross(B))
eq('Maxwell momentum balance',dt(S)+s.Matrix([sum(s.diff(Pi[i,j],X[j]) for j in range(3)) for i in range(3)])+force,zero)
assert force.subs({x:1,y:0,z:0,v:s.Rational(1,2)})!=zero
print(f'{len(checks)}/{len(checks)} PASS; SymPy {s.__version__}; nonzero matter-force guard PASS')
