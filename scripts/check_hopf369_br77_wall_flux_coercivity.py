#!/usr/bin/env python3
"""BR77 exact MOVING-wall positive ADM energy-flux estimate.

Given future unit timelike slice normal t, spacelike material normal s,
a=g(t,s), decompose s=-a t+r with g(r,t)=0, |r|²=1+a².
Let alpha=t·du, beta the four spatial derivatives in orthonormal H.
Physical normal energy E=(alpha²+|beta|²)/2 is positive at ANY ADM shift.
The EXACT stress-energy flux is
  T(t,s) = -a E + alpha (r·beta).
By positive Cauchy/Young (without boundary sign assumptions):
  |T(t,s)| <= (|a|+sqrt(1+a²)) E.
No glancing q denominator and NO artificial C>0 restriction.

For ADM/graph, a=t^mu F_mu/sqrt(z) with z=g^-1(F,F)>0.
The tilt coefficient is therefore actual source geometry. This
provides a quantitative wall-flux UPPER bound; it does NOT imply
Einstein–Israel dissipativity (equality of physical source and incoming
characteristics), normal H1 trace control, or global nonlinear PDE
continuation. The coefficient grows with wall tilt and must be bounded
on the physical continuation domain.

--part decomposition|sharp|channels|negative
"""
import argparse
from fractions import Fraction as F
from itertools import product

def sample(k):
    assert F(0)<=k<1
    a=2*k/(1-k*k)
    rho=(1+k*k)/(1-k*k)
    assert rho*rho==1+a*a
    return a,rho

def data():
    # Independent physical orthonormal tangent derivatives with signed
    # time derivative alpha. Rotational symmetry aligns spatial r to x4.
    alphas=[F(-7,5),F(0),F(1),F(11,7)]
    betas=[
      (F(3,7),F(-1,11),F(5,13),F(-2,17)),
      (F(0),F(1),F(-2),F(3)),
      (F(1,13),F(3,5),F(-5,7),F(9,11)),
    ]
    return alphas,betas

def decomposition():
    for k in (F(0),F(1,7),F(2,5),F(3,4)):
      a,rho=sample(k)
      for alpha,beta in product(*data()):
        E=(alpha*alpha+sum(v*v for v in beta))/2
        flux=-a*E+rho*alpha*beta[3]
        assert abs(flux)<=(a+rho)*E
        # Two independent exact sums of squares, for ±rho αβn:
        plus=rho*((alpha+beta[3])**2+sum(v*v for v in beta[:3]))/2
        minus=rho*((alpha-beta[3])**2+sum(v*v for v in beta[:3]))/2
        assert rho*E+rho*alpha*beta[3]==plus
        assert rho*E-rho*alpha*beta[3]==minus
        assert plus>=0 and minus>=0
    print('BR77 exact four-axis normal graph tilt positive flux estimate and two SOS certificates')

def sharp():
    for k in (F(0),F(1,3),F(2,3)):
      a,rho=sample(k)
      # alpha=+1,beta_n=-1 reaches flux=-(a+rho)E; exact sharpness.
      alpha=F(1);beta=(F(0),F(0),F(0),F(-1))
      E=(alpha*alpha+sum(v*v for v in beta))/2
      flux=-a*E+rho*alpha*beta[3]
      assert flux==-(a+rho)*E
      # Large tilt does NOT destroy energy positivity but it raises
      # the geometric flux coefficient; no uniform bound if z→0+.
    print('BR77 exact sharp moving-wall flux coefficient achieved in 3 independent tilts')

def channels():
    for dim in (15,5):
      k=F(3,5);a,rho=sample(k)
      totalE=F(0);totalFlux=F(0)
      for ch in range(dim):
        alpha=F((ch*3)%13-6,7)
        beta=tuple(F((ch+2)*(i+3)%17-8,11) for i in range(4))
        E=(alpha*alpha+sum(v*v for v in beta))/2
        flux=-a*E+rho*alpha*beta[3]
        assert abs(flux)<=(a+rho)*E
        totalE+=E;totalFlux+=flux
      assert abs(totalFlux)<=(a+rho)*totalE
    print('BR77 actual 15+5 principal scalar channels, single physical geometric tilt payment')

def negative():
    # A false fixed-wall estimate |flux|<=E fails for moving tilt.
    a,rho=sample(F(3,4))
    alpha=F(1);beta=F(-1)
    E=F(1);flux=-a*E+rho*alpha*beta
    assert abs(flux)>E and abs(flux)==(a+rho)*E
    print('BR77 REFUSAL: fixed Gaussian coefficient 1 cannot bound general moving-wall flux')

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--part',choices=['decomposition','sharp','channels','negative'],default='decomposition')
    a=p.parse_args()
    {'decomposition':decomposition,'sharp':sharp,
     'channels':channels,'negative':negative}[a.part]()

if __name__=='__main__':main()
