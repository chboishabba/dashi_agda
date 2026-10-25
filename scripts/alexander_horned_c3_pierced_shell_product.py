#!/usr/bin/env python3
"""Rational stereographic checks for the full pierced-shell collar.

The Alexander/Hatcher wild-sphere topology is NOT certified here.
This is the elementary homeomorphism for a finite spherical shell
pierced by one straight cylindrical spoke, not an infinite horn map.
"""
from fractions import Fraction as Q
from itertools import product
from math import sqrt,isclose
import json

A=Q(1,4); RMIN=Q(15,4); RMAX=Q(17,4)

def inverse_stereo(r,z1,z2):
    s=z1*z1+z2*z2
    t=Q(9)+r*(1-s)/(1+s)
    u=2*r*z1/(1+s)
    v=2*r*z2/(1+s)
    assert (t-9)**2+u*u+v*v==r*r
    assert t-(9-r)>0
    assert u/(t-(9-r))==z1 and v/(t-(9-r))==z2
    return t,u,v

def boundary_radius(r):
    return (float(r)+sqrt(float(r*r-A*A)))/float(A)

def audit():
    count=0
    for rv in (Q(151,40),Q(4),Q(169,40)):
        lim=boundary_radius(rv)
        assert lim>29
        for k,l in product(range(-8,9),repeat=2):
            z1,z2=Q(k,2),Q(l,2)
            assert float(z1*z1+z2*z2)<lim*lim
            t,u,v=inverse_stereo(rv,z1,z2)
            # In this shell, the only solid is the straight axial tube.
            in_tube=Q(1,2)<=t<=Q(17,2) and u*u+v*v<=A*A
            assert not in_tube
            count+=1
        inner_t=9-sqrt(float(rv*rv-A*A))
        z_boundary=float(A)/(inner_t-(9-float(rv)))
        assert isclose(z_boundary,lim,rel_tol=3e-12)
        assert isclose(2*float(rv)*lim/(1+lim*lim),float(A),rel_tol=3e-12)
    return {'r_inner':'15/4','r_outer':'17/4','tube_radius':'1/4',
            'chart':'z=v/(t-9+r); y=z/R(r)',
            'R(r)':'(r+sqrt(r^2-1/16))/(1/4)',
            'inverse':'t=9+r(1-|z|^2)/(1+|z|^2), v=2rz/(1+|z|^2)',
            'domain':'(15/4,17/4) x open unit disk',
            'exact_rational_samples':count,
            'global_topology_machine_proof':False}

if __name__=='__main__':
    print(json.dumps(audit(),indent=2))
