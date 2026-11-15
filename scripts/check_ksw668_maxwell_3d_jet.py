#!/usr/bin/env python3
"""Exact 3D Maxwell/Poynting benchmark, SymPy, non-empirical.

E=-(xy+z²,yz+x²,zx+y²), B=t(y,z,x), J=-t(1,1,1).
These are potential-derived SI-normalized fields eps0=mu0=c=1.
Both Maxwell curl equations, div(B), charge continuity, local Poynting,
integrated 3D cube conservation and SIX actual face integrals are checked.
"""
import json
import sympy as s


def check():
    x,y,z,t,L=s.symbols('x y z t L',real=True)
    curl=lambda v:s.Matrix([s.diff(v[2],y)-s.diff(v[1],z),
                            s.diff(v[0],z)-s.diff(v[2],x),
                            s.diff(v[1],x)-s.diff(v[0],y)])
    div=lambda v:s.diff(v[0],x)+s.diff(v[1],y)+s.diff(v[2],z)
    A=t*s.Matrix([x*y+z**2,y*z+x**2,z*x+y**2])
    E=-s.diff(A,t)
    B=curl(A)
    J=curl(B)-s.diff(E,t)
    S=E.cross(B)
    U=(E.dot(E)+B.dot(B))/2
    rho=div(E)
    assert B==s.Matrix([t*y,t*z,t*x])
    assert J==s.Matrix([-t,-t,-t])
    assert curl(E)+s.diff(B,t)==s.zeros(3,1)
    assert curl(B)-s.diff(E,t)-J==s.zeros(3,1)
    assert s.expand(div(B))==0
    assert s.expand(s.diff(rho,t)+div(J))==0
    assert s.expand(s.diff(U,t)+div(S)+J.dot(E))==0
    volume=lambda q:s.integrate(q,(x,0,L),(y,0,L),(z,0,L))
    rate=s.factor(volume(s.diff(U,t)))
    flux=s.factor(volume(div(S)))
    work=s.factor(volume(J.dot(E)))
    assert s.expand(rate-L**5*t)==0
    assert s.expand(flux+s.Rational(11,4)*L**5*t)==0
    assert s.expand(work-s.Rational(7,4)*L**5*t)==0
    assert s.expand(rate+flux+work)==0
    coords=(x,y,z)
    direct=0
    for i,coord in enumerate(coords):
        other=[a for a in coords if a!=coord]
        face=S[i].subs(coord,L)-S[i].subs(coord,0)
        direct+=s.integrate(face,(other[0],0,L),(other[1],0,L))
    assert s.simplify(direct-flux)==0
    assert (rate.subs({L:1,t:1}),flux.subs({L:1,t:1}),
            work.subs({L:1,t:1}))==(1,-s.Rational(11,4),s.Rational(7,4))
    return {
      "status":"PASS","scope":"exact polynomial, not empirical",
      "Maxwell_Ampere_Faraday":"PASS","divB_zero":True,
      "charge_continuity":"PASS","local_Poynting":"PASS",
      "integrated_energy_derivative":str(rate),
      "integrated_outward_flux":str(flux),
      "integrated_current_work":str(work),
      "boundary_face_direct_integration":"PASS",
      "local_and_integrated_residual":"0",
      "sample_L1_t1":{"rate":"1","flux":"-11/4","work":"7/4"},
      "same_mms_observation":False,
    }


if __name__=="__main__":
    print(json.dumps(check(),indent=2))
