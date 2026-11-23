#!/usr/bin/env python3
"""Driven Landau superconducting order parameter with signed power ports.

Minimal scalar amplitude / relaxational dynamics only; not anisotropic
multi-band YBCO TDGL, vortex physics, external gravity, or source fit.
Donors: SmithFilsingerDispersiveMaterialPort and LiTorr constitutive/source.
"""
import sympy as s
def check():
    x,T,Tc,a,b,k,u,Gamma=s.symbols("x T Tc a b k u Gamma",real=True)
    F=a*(T-Tc)*x**2/2+b*x**4/4-k*u*x
    Fx=s.diff(F,x)
    FT=s.diff(F,T)
    Fu=s.diff(F,u)
    Tdot,udot=s.symbols("Tdot udot",real=True)
    xdot=-Gamma*Fx
    dF=s.expand(Fx*xdot+FT*Tdot+Fu*udot)
    assert s.simplify(dF+Gamma*Fx**2-FT*Tdot-Fu*udot)==0
    ordered=s.symbols("ordered",positive=True)
    assert s.simplify(Fx.subs(u,0).subs(x,ordered)
       .subs(ordered**2,a*(Tc-T)/b))==0
    Omega=s.symbols("Omega",real=True)
    assert s.diff(F,Omega)==0
    print("PASS exact scalar Landau relaxation: dF=-Gamma Fx²+FT*Tdot+Fu*udot")
    print("No mechanical RPM or gravitational output law follows from GL potential alone.")
    print("OPEN: full gauge-covariant YBCO TDGL, flux pinning, measured pump field and stress-energy")
if __name__=="__main__":check()
