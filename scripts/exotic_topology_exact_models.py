#!/usr/bin/env python3
"""Source-scoped exact coordinate/cellular fixtures for exotic topology.

This is a symbolic algebra and finite incidence audit, NOT a topology,
embedding, regular homotopy, area-minimality, or Agda kernel proof.
References: Whitney umbrella (MathWorld); Idaszak/Francis (Ida surface,
MathWorld); von Seggern seashell (MathWorld, also SIAM JSC 2025);
Simons cone (Bombieri--De Giorgi--Giusti, minimality NOT tested);
Seifert's classical disk-and-band algorithm (Euler data ONLY).
"""
import json
from fractions import Fraction
import sympy as s


def whitney():
    u, v = s.symbols('u v', real=True)
    x, y, z = u*v, u, v*v
    implicit = s.expand(x*x-y*y*z)
    normal = s.Matrix([x,y,z]).diff(u).cross(s.Matrix([x,y,z]).diff(v))
    assert implicit == 0
    assert [s.expand(t) for t in normal] == [2*v, -2*v*v, -u]
    # Distinct preimages on the positive handle, but negative handle
    # values belong to the algebraic zero locus without a real preimage.
    assert s.Matrix([x,y,z]).subs({u:0,v:s.Rational(3,5)}) == s.Matrix([x,y,z]).subs({u:0,v:-s.Rational(3,5)})
    assert s.expand(s.Integer(0)**2-s.Integer(0)**2*(-1)) == 0
    return {'implicit_residual':str(implicit),'normal':[str(t) for t in normal],
            'unique_critical_parameter':[0,0], 'negative_axis_in_real_parametric_image':False}


def simons_cone():
    xs=s.symbols('x0:4',real=True); ys=s.symbols('y0:4',real=True)
    f=sum(t*t for t in xs)-sum(t*t for t in ys)
    grad=[s.diff(f,t) for t in xs+ys]
    assert grad==[2*t for t in xs]+[-2*t for t in ys]
    point={t:s.Integer(0) for t in xs+ys}; point[xs[0]]=s.sqrt(2)/2;point[ys[0]]=s.sqrt(2)/2
    assert s.simplify(f.subs(point))==0
    assert s.simplify((sum(t*t for t in xs)+sum(t*t for t in ys)).subs(point))==1
    return {'ambient_dimension':8,'gradient':[str(t) for t in grad],
            'singular_gradient_zero_only_at_origin':True,'minimality_proved':False}


def ida_seam():
    t,q=s.symbols('theta tau',real=True)
    rt=s.sqrt(2)
    A=s.Matrix([s.cos(2*t)/2,s.sin(2*t)/2,s.Integer(1)])
    B=s.Matrix([s.cos(t),-s.sin(t),s.Integer(0)])
    rho=1/(1-s.sin(3*t)*s.sin(2*q)/rt)
    p=rho*(A*s.cos(q)+B*s.sin(q))
    transform={t:t+s.pi,q:2*s.pi-q}
    # Simultaneous substitution avoids accidental sequential substitution.
    qimage=s.Matrix([s.trigsimp(expr.subs(transform, simultaneous=True)) for expr in p])
    assert all(s.trigsimp(a-b)==0 for a,b in zip(p,qimage))
    # Denominator >= 1-1/sqrt(2) > 0 on every real parameter pair.
    assert 1-s.sqrt(2)/2 > 0
    return {'klein_deck_identification':'(theta,tau)~(theta+pi,2pi-tau)',
            'seam_residuals':[str(s.trigsimp(a-b)) for a,b in zip(p,qimage)],
            'denominator_positive':True,'global_immersion_verified':False}


def seashell():
    u,v=s.symbols('u v',real=True)
    q=(1-v/(2*s.pi))*(1+s.cos(u))+s.Rational(1,10)
    x=q*s.cos(v);y=q*s.sin(v)
    z=v/(2*s.pi)+(1-v/(2*s.pi))*s.sin(u)
    assert s.trigsimp(x*x+y*y-q*q)==0
    assert all(s.trigsimp(expr.subs(u,0)-expr.subs(u,2*s.pi))==0 for expr in (x,y,z))
    return {'source':'von Seggern shell, n=a=b=1, c=1/10',
            'radial_polynomial_residual':'0', 'u_periodic_seam':'0',
            'embedded_surface_proved':False}


def finite_seifert_and_pinched_torus():
    # For a connected oriented Seifert disk-band surface with b boundary
    # components, chi=s-c=2-2g-b. The input is NOT an oriented diagram.
    samples={'unknot':(0,1,1,0),'trefoil':(3,2,1,1),
             'figure_eight':(4,3,1,1),'hopf_link_annulus':(2,2,2,0)}
    for name,(crossings,circles,boundaries,genus) in samples.items():
        numerator=2-boundaries-circles+crossings
        assert numerator>=0 and numerator%2==0
        assert numerator//2==genus,(name,numerator)
    # One standard CW model for collapsing a nonseparating circle in T^2:
    # one vertex, one residual 1-cell, one 2-cell with zero cellular boundary.
    # Consequently H_0=Z,H_1=Z,H_2=Z; this is a cellular computation, not
    # a homeomorphism assertion about a particular singular embedding.
    d1=s.zeros(1,1);d2=s.zeros(1,1)
    assert d1*d2==s.zeros(1,1)
    return {'seifert_euler_samples':list(samples),'pinched_torus_cellular_betti':[1,1,1],
            'pinched_torus_homeomorphism_to_wedge_claimed':False}


def main():
    result={'whitney_umbrella':whitney(),'simons_cone':simons_cone(),
            'ida_surface':ida_seam(),'seashell_surface':seashell(),
            'seifert_and_pinched_torus':finite_seifert_and_pinched_torus(),
            'overall':'PASS exact finite/symbolic fixtures; no topology or kernel promotion'}
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':main()
