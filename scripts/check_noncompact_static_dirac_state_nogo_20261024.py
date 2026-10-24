#!/usr/bin/env python3
"""Scoped 2D CFT obstruction: stationary noncompact line vs closed circle.

Massless conformal Dirac state on global optical LINE with flat vacuum
asymptotics has constant chiral t_+/-; t_+=t_-=0. Patching negative
circle Casimir t to zero is NOT a conserved static state of this free CFT.
Does NOT exclude MMP's CLOSED-LOOP state or general interacting 4D QFT.
"""
import math
import sympy as s
from scipy.integrate import quad
c,t,tp,F,Fp,N=s.symbols('c t tp F Fp N',real=True,nonzero=True)
rho=c*Fp/(12*s.pi)+c*F*F/(24*s.pi)+2*t/N**2
pr=-c*F*F/(24*s.pi)+2*t/N**2
prprime=-c*F*Fp/(12*s.pi)-4*t*F/N**2+2*tp/N**2
assert s.simplify(prprime+F*(rho+pr)-2*tp/N**2)==0
assert s.simplify(rho.subs({F:0,Fp:0,N:1})-2*t)==0
# If t=0 and F/N dies at ±infinity, integration by parts:
# int dx (rho+p)/N = c/(12pi) int dx F²/N >= 0 (2D only).
nu=lambda x:1+.2*math.exp(-x*x)
f=lambda x:-.4*x*math.exp(-x*x)/nu(x)
fp=lambda x:-.4*math.exp(-x*x)*(1-2*x*x)/nu(x)-f(x)**2
lhs=quad(lambda x:fp(x)/nu(x),-12,12,epsabs=1e-12)[0]/(12*math.pi)
rhs=quad(lambda x:f(x)**2/nu(x),-12,12,epsabs=1e-12)[0]/(12*math.pi)
assert lhs>0 and abs(lhs-rhs)<1e-12
print('PASS: static 2D Ward requires tprime=0 absent extra source')
print('PASS: vacuum asymptotics force t=0 on globally noncompact line')
print('PASS: 2D null integral equals positive anomaly-gradient integral',lhs)
print('OPEN: 4D weighted ANEC, genuine MMP closed-loop state and nonlocal 4D stress')
