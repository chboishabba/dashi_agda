#!/usr/bin/env python3
"""Weak-field GR Lense-Thirring orbit-average and conditional KK discriminator.
Not a tracking-data fit or an Earth solution of nontrivial 5D field equations.
"""
import math
from scipy.integrate import quad
from scipy.constants import G, c

YEAR = 365.256363004 * 86400.
MAS_PER_RAD = (180. / math.pi) * 3600. * 1000.
EARTH_J = 5.86e33  # approximate kg m^2 / s

def lt_rate(a, e, J=EARTH_J):
    return 2. * G * J / (c*c*a**3*(1.-e*e)**1.5)

def mean_inverse_r3(a, e):
    # Eccentric anomaly; dt / P = (1-e cos E)dE/(2pi).
    f = lambda E: 1. / (a**3 * (1.-e*math.cos(E))**2)
    return quad(f, 0., 2.*math.pi, epsabs=1e-31, epsrel=1e-12)[0] / (2.*math.pi)

def verify(label, a, e):
    formula = 1. / (a**3 * (1.-e*e)**1.5)
    numerical = mean_inverse_r3(a,e)
    assert abs(numerical/formula-1.) < 2e-12
    rate = lt_rate(a,e) * YEAR * MAS_PER_RAD
    print(f"{label}: {rate:.6f} mas/yr (illustrative input)")
    return rate

if __name__ == "__main__":
    low = verify("Original LARES class", 7820e3, .001)
    high = verify("LARES-2/LAGEOS-class", 12270e3, .0045)
    assert low > high > 0
    # Toy uniform exterior ratio: g_tphi = (1+delta) g_tphi^GR.
    delta = .01
    assert math.isclose((1+delta)*lt_rate(12270e3,.0045)/lt_rate(12270e3,.0045),1.01)
    print("PASS orbit average and conditional metric-scale test")
    print("WARNING: delta is phenomenological, not a prediction of a 5D solution")
