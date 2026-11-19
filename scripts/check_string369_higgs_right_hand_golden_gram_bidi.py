#!/usr/bin/env python3
"""Right-hand Higgs plane, golden determinant discriminator, gyroscopic BIDI.

Original DASHI RightHandRule369Exact, selected quotient Gram checker,
CarrierHiggsMassReceipt and SmithFilsinger nonlinear quadrature.
Classical metric-compatible Hodge rotation and gyroscopic oscillator.
Cube-root match is POST HOC; no physical determinant exponent or
Lorentz-invariant gyroscopic background is derived.
"""
import sympy as s
import numpy as np
G=s.Matrix([[s.Rational(1526,13471),s.Rational(1616,13471)],
 [s.Rational(1616,13471),s.Rational(238495303,76582635)]])
assert G.det()==s.Rational(25914758,76582635)
rho=G[0,1]/s.sqrt(G[0,0]*G[1,1])
J=s.Matrix([[0,-1],[1,0]])
A=s.sqrt(G.det())*G.inv()*J
assert s.simplify(A*A+s.eye(2))==s.zeros(2)
assert s.simplify(A.T*G+G*A)==s.zeros(2)
a,b,g,w=s.symbols('a b g w',real=True)
D=s.diag(a,b)-w*w*s.eye(2)+2*s.I*w*g*J
assert s.expand(D.det()-((a-w*w)*(b-w*w)-4*w*w*g*g))==0
v=246.22;m0=(1+5**.5)/2*v/np.pi;m=125.065
rho=float(rho);det=1-rho*rho
print('rho, angle, area',rho,np.degrees(np.arccos(rho)),np.sqrt(det))
for e in (0,1,.5,.25,1/3):
    print('POST HOC determinant exponent, candidate GeV, error',e,m0*det**e,m0*det**e-m)
print('inverse exponent',np.log(m/m0)/np.log(det))
assert abs(m0*det**(1/3)-125.06390101108863)<1e-10
for M in (200,500,1000):
    gamma=np.sqrt((m0*m0-m*m)*(M*M-m*m)/(4*m*m))
    poles=np.sqrt(np.sort(np.roots([1,-(m0*m0+M*M+4*gamma*gamma),m0*m0*M*M])))
    assert abs(poles[0]-m)<1e-10
    print('conditional gyroscopic heavy mass, gamma, poles',M,gamma,poles)
print('OPEN independently derive determinant exponent, physical metric, Hessian and rotational background')
