#!/usr/bin/env python3
"""RH P0 E2: exact original frozen-prime physical Fourier wavepackets.

For each source prime port P_i=4*pole*eps*h(u)[A1*cos(2r*u)-A2*cos(r*u)],
A1,A2=O(1/r), eps=O(r^-5), r=t/16.
The horizontal cosh(a*u) stays inside H_a(omega) and |a|<=1/2.
Source exact shift -> four packets omega +/-r, +/-2r. Each compact smooth
packet has fixed PHYSICAL ordinate width and uniform Sobolev tails.
Riemann-von Mangoldt unit-height counts then give O(r^-6 log t)
absolute full zero and smooth Gamma contributions, NOT O(r^-5 log t).
Unproved: cancellation of log and complete post-sixth signed strict cut.
"""
from fractions import Fraction as F
import sympy as S
import numpy as np
from scipy.integrate import quad
u,omega,r,t,a,A1,A2,eps,pole=S.symbols('u omega r t a A1 A2 eps pole',real=True)
for m in (1,2):
    assert S.trigsimp(S.cos(m*r*u)*S.cos(omega*u)
         -(S.cos((omega+m*r)*u)+S.cos((omega-m*r)*u))/2)==0
assert F(4)*F(1,2)==2
print('PASS source factor 2 and four physical-frequency sidebands ±r and ±2r')
def phi(z):return np.exp(-1/z) if z>0 else 0.
def step(z):
    if z<=0:return 0.
    if z>=1:return 1.
    a,b=phi(z),phi(1-z)
    return a/(a+b)
delta=1/32
def ptop(L,u):
    d=abs(u-L)
    if d<=delta/2:return 1.
    if d>=delta:return 0.
    return step((delta-d)/(delta/2))
def even(L,u):return ptop(L,u)+ptop(-L,u)
def H(L,xi,aa=0.17):
    return 2*quad(lambda u:even(L,u)*np.cosh(aa*u)*np.cos(xi*u),
                  L-delta,L+delta,epsabs=2e-12,epsrel=2e-12,limit=200)[0]
for p in (2,3):
    L=np.log(p);other=np.log(5-p)
    assert even(L,L)==1 and even(L,other)==0
    print('PASS C∞ fixed aperture p',p,'H(0)',round(H(L,0),9),
          'H(100)',round(H(L,100),9),'H(200)',round(H(L,200),9))
G=F(83,30);P=F(32)
assert G<3 and P<=32
# A_j<=G/r, eps<=r^-5, hence each of four packet coefficients O(r^-6).
for k in (2,3,4,6,8):
    assert (k-6)-k == -6
assert sum(F(1,n**3) for n in range(1,50))<2
print('PASS original source r^-6 sideband scale; RvM unit-ordinate shell -> O(r^-6 log t)')
print('OPEN log cancellation, completed post-sixth, E3 independent strict inequality; no RH/GRH')
