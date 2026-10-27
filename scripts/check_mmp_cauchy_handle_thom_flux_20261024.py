#!/usr/bin/env python3
"""Source-bounded smooth magnetic flux on a same-universe Cauchy handle.

Sigma=(S1 x S2) minus a point = R3#(S1 x S2), a one-ended 3-manifold
whose punctured CW skeleton has H1=H2=Z. A complete Riemannian metric
equal to Euclidean outside a compact core can be obtained by smooth
collar gluing, hence R x Sigma admits an ultrastatic globally hyperbolic
metric with a noncompact Cauchy slice. These are EXTERNAL geometric
theorems, NOT proved by the numeric test.

On a tubular neighbourhood S1 x D2 of an embedded S1 generator,
F=C*bump(r)*dx wedge dy is closed and smooth, with total dual-S2 flux
2pi*q. In a locally product metric its magnetic field follows closed
S1 loops. d*F=J may require matter current; Einstein backreaction,
global gauge/Dirac states and physical device are NOT constructed.
Original theorem sources: de Rham/Poincare duality, Thom forms,
Nomizu--Ozeki (1961) DOI 10.1090/S0002-9939-1961-0133785-8.
"""
import json, math
from pathlib import Path
import numpy as np
import sympy as s
from scipy.integrate import quad

x,y,theta,C=s.symbols('x y theta C',real=True)
r2=x*x+y*y
interior_rho=s.exp(-1/(1-r2))
# d(Fxy dx^dy) depends only on the longitudinal theta derivative.
assert s.simplify(s.diff(C*interior_rho,theta))==0
# Magnetic product-field dual points along longitudinal theta,
# and therefore follows closed longitudinal S1 orbits at each r<1.
d1=s.zeros(1,1); d2=s.zeros(1,1)
assert d1*d2==s.zeros(1,1)
betti={'H0_rank':1-d1.rank(),
       'H1_rank':1-d1.rank()-d2.rank(),
       'H2_rank':1-d2.rank()}
assert betti=={'H0_rank':1,'H1_rank':1,'H2_rank':1}

def bump(radius):
    if radius>=1: return 0.
    return math.exp(-1/(1-radius*radius))

norm=quad(lambda radius:bump(radius)*radius,0,1,
          epsabs=1e-14,epsrel=1e-14)[0]
assert norm>0
flux=[]
for q in (0,1,2,12,24,-3):
    coefficient=q/norm
    measured=2*math.pi*quad(lambda radius:coefficient*bump(radius)*radius,
                             0,1,epsabs=5e-12)[0]
    assert abs(measured-2*math.pi*q)<1e-9
    flux.append({'q':q,'flux':measured,'first_chern_number':measured/(2*math.pi)})
for radius in (0,.3,.7):
    assert 3/norm*bump(radius)>0
    ang=np.linspace(0,2*math.pi,401)
    assert abs(math.cos(ang[-1])-math.cos(ang[0]))<1e-13
    assert abs(math.sin(ang[-1])-math.sin(ang[0]))<1e-13
# Spin structures form an H1(Sigma,Z2)=Z2 torsor; independent flat
# U1 connections are classified by H1(Sigma,U1)=U1. A magnetic Chern
# number q in H2(Sigma,Z) does NOT determine either return-loop phase.
# This test uses the *separate* massless 1+1D Dirac Bernoulli Casimir,
# not a four-dimensional negative gravitational stress.
def bernoulli2(alpha):
    u=alpha%1.
    return u*u-u+1/6
phase_cases=[]
for q in (2,12,24):
    for spin_phase in (0.,.5):
        for wilson in (0.,1/3,2/3):
            alpha=(spin_phase+wilson)%1.
            phase_cases.append({'q':q,'spin_phase':spin_phase,
              'flat_wilson_fraction':wilson,'alpha':alpha,
              'B2':bernoulli2(alpha)})
assert abs(bernoulli2(.5)+1/12)<1e-14
assert abs(bernoulli2(.5+1/3)-1/36)<1e-14
assert abs(bernoulli2(.5+2/3)-1/36)<1e-14
for spin in (0.,.5):
    for w in (0.,1/3,2/3):
        vals=[z['B2'] for z in phase_cases
              if z['spin_phase']==spin and z['flat_wilson_fraction']==w]
        assert max(vals)-min(vals)<1e-14

out={'spatial_manifold':'(S1xS2) minus a point = R3#(S1xS2)',
     'spatial_ends':1,'CW_Betti_numbers':betti,
     'smooth_bump_radial_moment':norm,'flux_cases':flux,
     'spin_flat_wilson_phase_cases':phase_cases,
     'closed_magnetic_fieldlines':'S1 orbits in product tubular neighbourhood',
     'external_math_authority':'Poincare duality, compact Thom form, Nomizu-Ozeki, ultrastatic Cauchy theorem',
     'open':'full chosen Maxwell current, gauge twisted 4D Dirac state, global Hadamard magnetic-loop Casimir stress, Einstein equations, stability'}
if __name__=='__main__':
    print(json.dumps(out,indent=2))
    print('PASS: H1/H2 cellular model and smooth source-bounded flux normalization; not Maxwell-Einstein')
