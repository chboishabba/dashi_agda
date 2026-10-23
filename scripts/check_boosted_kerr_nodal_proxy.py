#!/usr/bin/env python3
"""First-order spin-orbit Hamiltonian nodal average for boosted-Kerr quotient.
Keeps physical J4 fixed; uses unperturbed Kepler ellipses and omits spin-independent
KK orbital changes. Not a full satellite orbit fit or nontrivial Earth matter model.
"""
import math
from scipy.integrate import quad
M=3.986004418e14/299792458.**2

def nodal_ratio(a,e,alpha):
    q=math.sinh(alpha)**2
    def av(correction):
        return quad(lambda E:(1-e*math.cos(E))**(-2)/
            math.sqrt(1+2*M*q/(a*(1-e*math.cos(E))))**int(correction),
            0,2*math.pi,epsrel=2e-13)[0]
    return av(True)/av(False)

for a,e in ((7820e3,.001),(12270e3,.0045)):
    for alpha in (0.,.3,1.):
        q=math.sinh(alpha)**2
        value=nodal_ratio(a,e,alpha)
        first_order=1-M*q/a*(1+e*e/2)/(1-e*e)
        assert abs(value-first_order)<3e-15
        print(f"a={a/1e3:.0f} km alpha={alpha}: spin-orbit nodal proxy ratio={value:.15f}, delta={value-1:+.4e}")
print("PASS leading spin-orbit nodal proxy and asymptotic expansion")
print("WARNING other metric potentials, matter coupling, Earth interior not included")
