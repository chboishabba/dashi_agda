#!/usr/bin/env python3
"""Exact weak-drive Lorentzian ODMR fluorescence model and magnetic sensitivity.
Phenomenological model, not a derivation from NV Lindblad dynamics.
All frequencies share one unit; gamma in frequency/magnetic-field units.
"""
import sympy as s
delta, linewidth, contrast, bright, bg, gamma=s.symbols(
    "delta linewidth contrast bright bg gamma",real=True)
L=linewidth**2/(delta**2+linewidth**2)
mu=bright*(1-contrast*L)+bg
dmu_ddelta=s.factor(s.diff(mu,delta))
assert s.simplify(dmu_ddelta-2*bright*contrast*linewidth**2*delta/(delta**2+linewidth**2)**2)==0
assert s.simplify(dmu_ddelta.subs(delta,linewidth)-bright*contrast/(2*linewidth))==0
assert s.simplify(dmu_ddelta.subs(delta,-linewidth)+bright*contrast/(2*linewidth))==0
# For delta = f_drive-(D+gamma B), derivative wrt B is -gamma*dmu/ddelta.
dmu_dB=-gamma*dmu_ddelta
assert s.simplify(dmu_dB.subs(delta,linewidth)+gamma*bright*contrast/(2*linewidth))==0
# Shot-noise Fisher information for Poisson count with mean mu (mu>0).
FI=s.factor(dmu_dB**2/mu)
assert s.simplify(FI.subs(delta,linewidth)-
    gamma**2*bright**2*contrast**2/
    (4*linewidth**2*(bright*(1-contrast/2)+bg)))==0
# Exact midpoint vs detuning symmetry and antisymmetric derivative.
assert s.simplify(mu.subs(delta,-delta)-mu)==0
assert s.simplify(dmu_ddelta.subs(delta,-delta)+dmu_ddelta)==0
print("PASS Lorentzian ODMR symmetry, derivative, signed B response, Poisson FI")
print("CONDITIONS linewidth>0; bright>0; bg>=0; 0<contrast<1; mu>0")
print("BOUNDARY phenomenological linewidth/contrast; microwave pumping and sample noise uncalibrated")
