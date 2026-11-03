#!/usr/bin/env python3
"""Restricted MMP ultrastatic product obstruction, not a 4D wormhole no-go.

Original sources: Maldacena--Milekhin--Popov (2018/2023) charged-fermion
wormhole; Polyakov/Casimir massless Dirac cylinder; Zahn (2014) locally
covariant charged-Dirac renormalization. Uses existing PR #1248 optical
circle and same-action finite-current ideas without reattributing them.

ds²=-dt²+dx²+R² dOmega², x~x+L. Only a spherical magnetic Maxwell field
and |q| ideal massless Dirac LLL species of a prescribed spin/Wilson phase.
Excludes extra matter, finite-radius dynamics, massive modes, curvature
counterterms and the *actual* noncompact MMP magnetic-return geometry.
"""
import json
import math
import sympy as s

L,R,e,G,c,Q,a=s.symbols("L R e G c Q a", positive=True)
B2=a*a-a+s.Rational(1,6)
Ef=2*s.pi*c*Q*B2/L
Em=s.pi*L*Q**2/(2*e**2*R**2)

def source(E):
    return tuple(map(s.simplify,(
        E/(4*s.pi*R**2*L),
        -s.diff(E,L)/(4*s.pi*R**2),
        -s.diff(E,R)/(8*s.pi*R*L))))

rf,pf,tf=source(Ef)
rm,pm,tm=source(Em)
assert s.simplify(pf-rf)==0 and tf==0
assert s.simplify(pm+rm)==0 and s.simplify(tm-rm)==0

# Maxwell F_theta_phi = q sin(theta)/(2e) has J^x=0.
# Phase theta_W=2*pi*(alpha-spin), so J^x is proportional to dE/dtheta_W.
Jx=s.simplify(s.diff(Ef,a)/(2*s.pi*4*s.pi*R**2))
nullmatter=s.factor(rf+pf+rm+pm)
assert s.simplify(nullmatter-2*rf)==0
# G_tt=+1/R², G_xx=-1/R² for flat(1+1) x round(S²).
Gkk=s.cancel(1/R**2-1/R**2)
einstein_null_residual=s.factor(Gkk-8*s.pi*G*nullmatter)
assert s.simplify(einstein_null_residual+16*s.pi*G*rf)==0
# If Einstein's radial-null condition demands B2=0, Maxwell's
# static no-current condition simultaneously demands B2'=0.
assert s.resultant(B2,s.diff(B2,a),a)!=0
assert s.simplify(B2.subs(a,s.Rational(1,2)))==-s.Rational(1,12)

def energy(l,r,q,alpha,charge=1.2):
    return 2*math.pi*q*(alpha*alpha-alpha+1/6)/l + math.pi*l*q*q/(2*charge*charge*r*r)

def numeric(alpha):
    l,r,q=7.2,3.1,12
    h=2.e-5
    gradL=-(energy(l+h,r,q,alpha)-energy(l-h,r,q,alpha))/(2*h)/(4*math.pi*r*r)
    gradR=-(energy(l,r+h,q,alpha)-energy(l,r-h,q,alpha))/(2*h)/(8*math.pi*r*l)
    gradTh=(energy(l,r,q,alpha+h/(2*math.pi))-energy(l,r,q,alpha-h/(2*math.pi)))/(2*h)/(4*math.pi*r*r)
    sub={L:l,R:r,Q:q,a:alpha,c:1,e:1.2}
    predicted=[pf+pm,tf+tm,Jx]
    errors=[abs(z-float(y.subs(sub))) for z,y in zip([gradL,gradR,gradTh],predicted)]
    assert max(errors)<1.e-9,errors
    return dict(alpha=alpha,source_gradient_errors=errors,
                radial_null_source=float(nullmatter.subs(sub)),
                required_Maxwell_Jx=float(Jx.subs(sub)))

rows=[numeric(float(a0)) for a0 in
      [0.5,1/6,5/6,(1-1/math.sqrt(3))/2]]
assert abs(rows[0]["required_Maxwell_Jx"])<1.e-12
assert abs(rows[0]["radial_null_source"])>1.e-6
assert abs(rows[-1]["radial_null_source"])<1.e-12
assert abs(rows[-1]["required_Maxwell_Jx"])>1.e-6
print(json.dumps({"Einstein_radial_null_mismatch":str(einstein_null_residual),
                  "Maxwell_Jx":str(Jx),
                  "B2":str(B2),
                  "B2_and_derivative_resultant":str(s.resultant(B2,s.diff(B2,a),a)),
                  "tests":rows,
                  "scope":"restricted ultrastatic product + ideal LLL + magnetic-only Maxwell",
                  "open":"actual 4D noncompact Hadamard and Einstein-Maxwell-Dirac state"},
                 indent=2))
print("PASS same functional variations, radial null mismatch and static Maxwell-current discriminator")
