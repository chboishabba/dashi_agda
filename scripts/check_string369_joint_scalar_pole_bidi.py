#!/usr/bin/env python3
"""Original restricted scalar potential + oriented Gram + dynamical BIDI.
Original #1106 and #1241 V6, orbifold comparison stationary branch;
#1531 inherited quotient Gram and right-hand completion.
Conditional cross-model identification; no physical CY pole prediction.
"""
import sympy as s
import numpy as np
from scipy.linalg import eigh
x,y,z,t,l,r=s.symbols('x y z t l r',real=True)
mu=3+(2*l-s.Rational(13,2))*t*t
V=(x*x-1)**2+(y*y+z*z-1)**2+2*y*y*z*z+x*x*z*z-mu*z*z+l*z**4
X=s.sqrt(1-t*t/2);Y=s.sqrt(1-2*t*t)
H=s.simplify(s.hessian(V,(x,y,z)).subs({x:X,y:Y,z:t}))
G=s.Matrix([[1,r,0],[r,1,0],[0,0,1-r*r]])
rho=s.sqrt(s.Rational(1616,13471)**2/(s.Rational(1526,13471)*s.Rational(238495303,76582635)))
D=1-rho*rho
N=H[:2,:2]; b=H[:2,2]; h=H[2,2]
assert s.simplify(h-(b.T*N.inv()*b)[0]-t*t*(8*l-26))==0
u=(-N.inv()*b).col_join(s.ones(1,1)); Z=s.simplify((u.T*G*u)[0])
assert s.simplify(Z-(1-r*r+t*t/(4*X**2)+4*t*t/Y**2+2*r*t*t/(X*Y)))==0
p={t:s.Rational('0.0246'),l:4,r:rho}; Hn=np.array(H.subs(p),float); Gn=np.array(G.subs(p),float)
a=eigh(Hn,eigvals_only=True); c=eigh(Hn,Gn,eigvals_only=True)
print('H',Hn,'poles',a,c,'ratio',np.sqrt(c[0]/a[0]),'Z',float(Z.subs(p)))
m0=float((1+s.sqrt(5))/2*s.Rational('246.22')/s.pi); target=m0*float(D)**(1/3); q=a[0]*(target/m0)**2
Nn=Hn[:2,:2]; bn=Hn[:2,2]; h0=Hn[2,2]
required=q*Gn[2,2]+bn@np.linalg.solve(Nn-q*Gn[:2,:2],bn); dl=(required-h0)/(8*.0246**2)
print('conditional joint mass',m0*np.sqrt(c[0]/a[0]),'required delta lambda',dl,'lambda',4+dl)
assert abs(eigh(Hn+np.diag([0,0,required-h0]),Gn,eigvals_only=True)[0]-q)<1e-12
F=np.array([[1,float(rho),0],[0,np.sqrt(float(D)),0],[0,0,np.sqrt(float(D))]])
assert np.allclose(F.T@F,Gn)
assert np.allclose(eigh(F.T@Hn@F,Gn,eigvals_only=True),a)
A=Nn-q*Gn[:2,:2]; target_s=h0-q*Gn[2,2]
num=bn@np.array([[A[1,1],-A[0,1]],[-A[1,0],A[0,0]]])@bn
gamma2=(np.linalg.det(A)-num/target_s)/(4*q)
Om=np.array([[0,-np.sqrt(gamma2),0],[np.sqrt(gamma2),0,0],[0,0,0]])
assert abs(np.linalg.det(Hn-q*Gn+2j*np.sqrt(q)*Om))<1e-10
T=np.block([[np.zeros((3,3)),np.eye(3)],[-np.linalg.solve(Gn,Hn),-2*np.linalg.solve(Gn,Om)]])
ev=np.linalg.eigvals(T)
assert max(abs(ev.real))<1e-9
assert abs(min(ev.imag[ev.imag>0])**2-q)<1e-10
print('conditional xy gyro gamma',np.sqrt(gamma2),'poles',np.sort(ev.imag[ev.imag>0])**2)
print('OPEN same-action physical Gram, scalar quartic, rotational source, pole and SI calibration')
