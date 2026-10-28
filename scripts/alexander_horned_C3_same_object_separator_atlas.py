#!/usr/bin/env python3
"""C3 Hatcher gluing: EXACT cap and cut-sphere geometry + explicit atlas.

The *infinite* supported wild satellite comes from Hatcher Ex 2B.2
and Lippert §§2.1-2.3, not from this finite coordinate checker.
Regular neighbourhood gluing, collar slides and van Kampen are
classical topological theorem inputs, not numerically certified.
"""
from fractions import Fraction as F
from itertools import product
from math import sqrt
import argparse,json

R=lambda x:(x[2],x[0],x[1])
C=((F(9),F(0),F(0)),(F(0),F(9),F(0)),(F(0),F(0),F(9)))
radius=F(4);epsilon=F(1,4);seed_radius=F(3,4)

def stereographic_inverse(u,v):
    # Sphere centred at 9e_i, radius 4; projection from
    # removed inner pole (t,u,v)=(5,0,0):
    # sigma(t,u,v)=(u/(t-5),v/(t-5)).
    # Its image for the sphere MINUS the tube disk is
    # the open disk |(u,v)| < 16 + sqrt(255).
    s=u*u+v*v
    t=(13+5*s)/(1+s);U=8*u/(1+s);V=8*v/(1+s)
    assert (t-9)**2+U*U+V*V==16
    assert U/(t-5)==u and V/(t-5)==v
    return t,U,V

def audit():
    assert tuple(map(R,C))==C[1:]+C[:1]
    assert R(R(R((1,2,3))))==(1,2,3)
    # Full endpoint disk inside unchanged radius-3/4 Hatcher cap:
    assert (F(1,2)**2+epsilon**2)==F(5,16)<seed_radius**2==F(9,16)
    # Explicit tame collar Phi(u,v,s)=(-sqrt(9/16-u²-v²)+s,u,v).
    assert seed_radius**2-epsilon**2==F(1,2)>F(1,8)**2
    # Sphere cuts do not meet nonincident balls/tubes:
    assert F(9)>radius+1
    assert F(162)>(2*radius)**2
    assert F(9)-epsilon>radius+epsilon
    assert F(1,2)<F(5)<F(17,2)<F(9)
    assert radius**2-epsilon**2==F(255,16)
    rho=16+sqrt(255)
    assert abs(rho*(16-sqrt(255))-1)<1e-11
    samples=0
    for a,b in product(range(-25,26),repeat=2):
        u,v=F(a,2),F(b,2)
        if float(u*u+v*v)>=rho*rho:continue
        stereographic_inverse(u,v);samples+=1
    cap=0
    for a,b in product(range(-16,17),repeat=2):
        u,v=F(a,64),F(b,64)
        if u*u+v*v>epsilon**2:continue
        rr=float(seed_radius**2-u*u-v*v)
        assert rr>=0.5
        for s in (-F(1,8),F(0),F(1,8)):
            x=-sqrt(rr)+float(s)
            norm2=x*x+float(u*u+v*v)
            if s>0:assert norm2<float(seed_radius**2)
            if s<0:assert norm2>float(seed_radius**2)
            assert abs(x+sqrt(rr)-float(s))<1e-12
        cap+=1
    return {'cut_spheres':3,'atlas_radius':'16 + sqrt(255)',
            'chart':'(t,u,v) -> (u/(t-5),v/(t-5))',
            'inverse':'t=(13+5|y|²)/(1+|y|²), u=8y1/(1+|y|²), v=8y2/(1+|y|²)',
            'overlap_contractible':'H_s(y)=(1-s)y',
            'stereographic_samples':samples,'cap_chart_samples':cap,
            'classical_supported_Hatcher_ball_required':True,
            'collar_van_Kampen_theorems_required':True,
            'infinite_embedding_machine_certified':False}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--json')
    args=p.parse_args();res=audit();print(json.dumps(res,indent=2))
    if args.json:
        from pathlib import Path
        Path(args.json).write_text(json.dumps(res,indent=2)+'\n')
