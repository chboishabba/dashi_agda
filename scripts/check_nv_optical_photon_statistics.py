#!/usr/bin/env python3
"""Exact symbolic NV photon-counting formulas; not an empirical calibration.
Poisson counts conditional on a calibrated expected mean mu >= 0.
The discrete likelihood does not by itself model detector deadtime,
afterpulsing, blinking, microwave pumping, or biological observables.
"""
import sympy as sp
mu=sp.symbols("mu", nonnegative=True, real=True)
n=sp.symbols("n", integer=True, nonnegative=True)
P=lambda k: sp.exp(-mu)*mu**k/sp.factorial(k)
assert sp.simplify(sp.summation(P(n),(n,0,sp.oo))-1)==0
assert sp.simplify(sp.summation(n*P(n),(n,0,sp.oo))-mu)==0
assert sp.simplify(sp.summation(n*n*P(n),(n,0,sp.oo))-mu-mu*mu)==0
N=sp.symbols("N", integer=True, positive=True)
p=sp.symbols("p", real=True)
bright,dark,bg=sp.symbols("bright dark bg", nonnegative=True, real=True)
mean=p*bright+(1-p)*dark+bg
assert sp.simplify(mean.subs(p,1)-bright-bg)==0
assert sp.simplify(mean.subs(p,0)-dark-bg)==0
assert sp.simplify(sp.diff(mean,p)-(bright-dark))==0
gaugeFlux, gain, B0=sp.symbols("F gain B0",real=True)
B=gain*gaugeFlux+B0
assert sp.simplify(sp.diff(B,gaugeFlux)-gain)==0
print("PASS: Poisson normalized, E[N]=mu, Var[N]=mu (under mu>=0)")
print("PASS: NV optical mixture endpoints/contrast derivative and curvature gain")
print("BOUNDARY: mu(B) must come from calibrated optical/microwave dynamics")
