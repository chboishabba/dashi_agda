#!/usr/bin/env python3
"""Independent deterministic numerical sanity check of the ANALYTIC
original SU(2) one-link conditional plaquette-variance lower bound.

Source proof:
  Docs/physics/YMClayOriginalSU2ConditionalVarianceNoncollapse20261109.md

This evaluates the true conditional one-link normalized Haar quaternion
density via stable quadrature in y=kappa*(1-q0), not a different Gibbs
model, but does NOT integrate the full lattice Wilson measure and is
NOT a proof of N1 continuum nontriviality or an Agda kernel receipt.
"""
import math


def simpson(fun, end, count=20000):
    assert count % 2 == 0 and end > 0
    h=end/count
    value=fun(0.)+fun(end)
    for i in range(1,count):
        value+=(4 if i%2 else 2)*fun(i*h)
    return value*h/3


def conditional_eigen_variances(kappa):
    assert kappa >= 0
    if kappa == 0:
        return .25,.25
    upper=min(2*kappa,60.)
    def weight(y):
        return math.exp(-y)*math.sqrt(max(0.,y*(2.-y/kappa)))
    z=simpson(weight,upper)
    xmean=simpson(lambda y:(1.-y/kappa)*weight(y),upper)/z
    x2mean=simpson(lambda y:(1.-y/kappa)**2*weight(y),upper)/z
    radial=x2mean-xmean*xmean
    transverse=(1.-x2mean)/3.
    return radial,transverse


def main():
    for kappa in (0.,.5,1.,6.,60.,600.):
        radial,transverse=conditional_eigen_variances(kappa)
        analytical_lower=1/(73728*(1+kappa)**2)
        assert min(radial,transverse)>=analytical_lower
        print("PASS kappa=",kappa,
              "radialVar=",round(radial,10),
              "transverseVar=",round(transverse,10),
              "rigorousLower=",round(analytical_lower,13))
    for beta in (1.,2.,6.,60.,600.):
        assert beta**2/(73728*(1+6*beta)**2) >= 1/3612672-1e-20
    print("PASS: universal beta-rescaled finite Wilson lower constant 1/3612672")
    print("UNPAID: original SU2 Haar-to-Agda source bridge, E1 tightness and N1 continuum")
if __name__=="__main__":
    main()
