#!/usr/bin/env python3
"""Exact symbolic certificates for the selected Gielis special case.

These are SymPy polynomial/trigonometric/calculus checks, NOT Agda
kernel acceptance, certified continuum spectral convergence or measured
physical optics.
"""
from __future__ import annotations
import json
import sympy as sp


def prove() -> dict:
    theta = sp.symbols("theta", real=True)
    m = sp.symbols("m", positive=True, integer=True)
    x = m * theta
    r = 2 / sp.sqrt(3 + sp.cos(x))

    assert sp.trigsimp(4*(sp.sin(theta)**4 + sp.cos(theta)**4) - (3+sp.cos(4*theta))) == 0
    assert sp.trigsimp(sp.diff(r,theta)-m*sp.sin(x)/(3+sp.cos(x))**sp.Rational(3,2)) == 0
    r2_expected = m**2*(sp.sin(x)**2+6*sp.cos(x)+2)/(2*(3+sp.cos(x))**sp.Rational(5,2))
    assert sp.trigsimp(sp.diff(r,theta,2)-r2_expected) == 0

    r1,r2 = sp.diff(r,theta),sp.diff(r,theta,2)
    curvature = (r*r+2*r1*r1-r*r2)/(r*r+r1*r1)**sp.Rational(3,2)
    assert sp.simplify(curvature.subs(theta,0)-(1-m*m/sp.Integer(8))) == 0
    assert sp.simplify(curvature.subs(theta,sp.pi/m)-(m*m+4)/(4*sp.sqrt(2))) == 0

    # Periodicity for integer m reduces the area integral to one period.
    # t=tan(phi/2), cos(phi)=(1-t^2)/(1+t^2).
    t = sp.symbols("t",real=True)
    transformed = sp.cancel((2/(1+t*t))/(3+(1-t*t)/(1+t*t)))
    assert sp.simplify(transformed-1/(2+t*t)) == 0
    halfangle_integral = sp.integrate(transformed,(t,-sp.oo,sp.oo))
    assert sp.simplify(halfangle_integral-sp.pi/sp.sqrt(2)) == 0
    area = 2*halfangle_integral
    assert sp.simplify(area-sp.sqrt(2)*sp.pi) == 0

    px,py,nx,ny,rx,ry=sp.symbols("px py nx ny rx ry",real=True)
    pin=sp.Matrix([px,py]);normal=sp.Matrix([nx,ny])
    origin=sp.Matrix([rx,ry])
    pout=pin-2*pin.dot(normal)*normal
    wall_impulse=pin-pout;ray_change=pout-pin
    cross=lambda a,b: sp.expand(a[0]*b[1]-a[1]*b[0])
    assert sp.expand(cross(origin,wall_impulse)+cross(origin,ray_change))==0
    energy=sp.factor(pout.dot(pout)-pin.dot(pin))
    assert sp.simplify(energy-4*pin.dot(normal)**2*(normal.dot(normal)-1))==0

    sine9=[(0,1,0,-1)[j%4] for j in range(36)]
    sine27=[(0,-1,0,1)[j%4] for j in range(36)]
    assert all(sine9[2*j]==sine27[2*j]==0 for j in range(18))
    assert (sine9[1],sine27[1])==(1,-1)

    return {
        "status":"exact_symbolic_identities_passed",
        "gielis_trigonometric_specialization":True,
        "radial_derivative":str(sp.diff(r,theta)),
        "radial_second_derivative":str(r2_expected),
        "area":str(area),
        "curvature_at_min_radius":str(1-m*m/sp.Integer(8)),
        "curvature_at_max_radius":str((m*m+4)/(4*sp.sqrt(2))),
        "curvature_negative_at_indentation_for_m_3_6_9":
            all(1-k*k/sp.Integer(8)<0 for k in (3,6,9)),
        "wall_ray_angular_impulse_balance":True,
        "specular_reflection_preserves_ray_norm_if_unit_normal":True,
        "c18_to_c36_oriented_sine_aliasing":True,
        "agda_kernel_accepted":False,
        "continuum_spectral_convergence_certified":False,
        "physical_optics_validated":False,
    }


if __name__ == "__main__":
    print(json.dumps(prove(),indent=2,sort_keys=True))
