#!/usr/bin/env python3
"""Hopf cutoff helicity, signed Fourier tail, aligned RMHD and GH coframe.
Analytic arguments are in the roadmap; these are symbolic regressions, not kernels.
"""
import sympy as s
from itertools import product, combinations
checks=[]
def eq(name,a,b):
    d=a-b
    if isinstance(d,s.MatrixBase): ok=all(s.factor(s.cancel(x))==0 for x in d)
    else: ok=s.simplify(d)==0
    assert ok,name
    checks.append(name)
x,y,z,t=s.symbols('x y z t',real=True); X=(x,y,z); D=1+x*x+y*y+z*z
B=8*s.Matrix([2*x*z-2*y,2*x+2*y*z,1-x*x-y*y+z*z])/D**3
T=4*(x*x+y*y)/D**2
G=s.Matrix([s.diff(T,i) for i in X]); eq('flux first integral',B.dot(G),0)
eq('div B',sum(s.diff(B[i],X[i]) for i in range(3)),0)
# In Hopf coordinates (t,xi,phi), primitive = H dxi+(M-H)dphi.
H,M,h=s.symbols('H M h',real=True)
eq('helicity wedge coefficient',H*h+(M-H)*h,M*h)
for n in range(5):
    f=t**n; primitive=t**(n+1)/(n+1); mass=s.Rational(1,n+1)
    eq('primitive derivative',s.diff(primitive,t),f)
    eq('helicity integral',s.integrate(mass*f,(t,0,1)),mass**2)
    eq('core endpoints',primitive.subs(t,1),mass)
# Actual smooth cutoff flux integral (u=t-tau); E1 derivative checked.
u=s.symbols('u',positive=True)
F=u*s.exp(-1/u)-s.expint(1,1/u)
eq('flat cutoff primitive',s.diff(F,u),s.exp(-1/u))
# Exact Fourier inverse-curl symbol on transverse modes; zero treated separately.
k1,k2,k3=s.symbols('k1 k2 k3',real=True); k=s.Matrix([k1,k2,k3]); v=s.Matrix(s.symbols('v1:4',real=True)); b=k.cross(v); ksq=k.dot(k)
A=s.I*k.cross(b)/ksq
eq('Fourier transverse',k.dot(b),0);eq('inverse curl',s.I*k.cross(A),b);eq('Coulomb gauge',k.dot(A),0)
# Relativistic ideal MHD, c=mu=1. K>|b|². gamma²=K/(K-|b|²).
q=s.Matrix(s.symbols('b1:4',real=True)); K,p0=s.symbols('K p0',positive=True); q2=q.dot(q); p=p0-q2/2; enthalpy=K-q2; e=enthalpy-p
for sign in (-1,1):
    vel=sign*q/s.sqrt(K); gamma2=K/enthalpy
    eq('RMHD timelike normalization',gamma2*(1-vel.dot(vel)),1)
    eq('RMHD ideal electric',vel.cross(q),s.zeros(3,1))
    eq('RMHD total spatial stress',enthalpy*gamma2*vel*vel.T+p*s.eye(3)+q2*s.eye(3)/2-q*q.T,p0*s.eye(3))
    eq('RMHD total energy',enthalpy*gamma2-p+q2/2,K-p0+q2)
    eq('RMHD momentum',enthalpy*gamma2*vel,sign*s.sqrt(K)*q)
    eq('RMHD particle flux squared prefactor',(enthalpy/K)*gamma2,1)
eq('stiff EOS',e-p,K-2*p0)
# GH coframe on punctured base: e0=V^-1/2 theta, ei=V^1/2 dxi;
# dtheta=*dV; a_i=V_i/(2V^1.5). Use coefficient 2-forms.
a=[0,*s.symbols('a1:4',real=True)]; unit=[s.eye(4)[:,i] for i in range(4)]
def wedge(u,v):return u*v.T-v*u.T
d=[s.zeros(4) for _ in range(4)]
for i in range(1,4):
    j,k=(i%3)+1,((i+1)%3)+1
    d[0]+=a[i]*wedge(unit[0],unit[i])+2*a[i]*wedge(unit[j],unit[k])
    for j in range(1,4):d[i]+=a[j]*wedge(unit[j],unit[i])
omega=[[s.zeros(4,1) for _ in range(4)] for _ in range(4)]
for i in range(1,4):
    omega[0][i]=-a[i]*unit[0]+sum((s.LeviCivita(i-1,j-1,k-1)*a[k]*unit[j] for j,k in product(range(1,4),repeat=2)),s.zeros(4,1))
    omega[i][0]=-omega[0][i]
for i,j in combinations(range(1,4),2):
    omega[i][j]=a[j]*unit[i]-a[i]*unit[j]-sum((s.LeviCivita(i-1,j-1,k-1)*a[k]*unit[0] for k in range(1,4)),s.zeros(4,1))
    omega[j][i]=-omega[i][j]
for i in range(4):eq('GH Cartan torsion',d[i]+sum((wedge(omega[i][j],unit[j]) for j in range(4)),s.zeros(4)),s.zeros(4))
for i in range(1,4):
    j,k=(i%3)+1,((i+1)%3)+1
    eq('GH chiral connection',omega[0][i],omega[j][k])
# North/south KK potentials in polar chart with dtheta=*dV, Chern -1.
th,m=s.symbols('theta m',positive=True); AN=m*(s.cos(th)-1); AS=m*(s.cos(th)+1)
eq('KK gauge difference',AS-AN,2*m);eq('KK curvature matching',s.diff(AN,th),s.diff(AS,th));eq('KK Chern',s.integrate(s.diff(AN,th),(th,0,s.pi))/(2*m),-1)
print(f'{len(checks)}/{len(checks)} exact checks PASS; SymPy {s.__version__}')
