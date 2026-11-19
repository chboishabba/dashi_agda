import sympy as s
import numpy as np
from scipy.optimize import brentq
from math import sqrt,atan
k,a,E=s.symbols('k a E',positive=True)
A,B=s.symbols('A B')
sol=s.solve([A-E-B/a**3,k*A-E+2*B/a**3],[A,B]); print('sphere',sol)
T=s.simplify(sol[A]/E); assert T==3/(k+2)
N,f=s.symbols('N f',positive=True)
T=1/(1+N*(k-1))
R=1-f+f*T
ki=s.solve(R-2,k)[0]; print('amplification inverse',s.factor(ki))
assert s.simplify(ki-(1-1/(N*(1+f))))==0
print('cancellation inverse',s.solve(R,k))
for L in [1/3,.8,.85,.9,.95,.99]:
    kval=float(ki.subs({N:L,f:.25})); print('N',L,'k for 2g',kval,'positive',kval>1e-12)
K0,h,m,q=s.symbols('K0 h m q',positive=True)
H=s.Matrix([[K0*q*q,h*q],[h*q,m]])
assert s.simplify(H.det()-q*q*(K0*m-h*h))==0
print('Schur stiffness',K0-h*h/m)
D=s.symbols('D',positive=True)
print('finite wavevector stiffness',K0-h*h/(m+D*q*q))
def Nz(r):
    e=sqrt(1/r**2-1); return (1+e**2)/e**3*(e-atan(e))
for f0 in [.25,1e-5]:
    for frac in [.5,.9]:
        n0=1/(1+f0)+frac*(1-1/(1+f0)); r=brentq(lambda r:Nz(r)-n0,1e-9,.99,xtol=1e-15)
        k0=1-1/(n0*(1+f0)); print('f',f0,'N',n0,'c/a',r,'k',k0,'coupling fraction',sqrt(1-k0)); assert abs(1-f0+f0/(1+n0*(k0-1))-2)<1e-8
print('PASS oblate inverse')
