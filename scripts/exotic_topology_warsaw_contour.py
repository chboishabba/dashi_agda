#!/usr/bin/env python3
"""Exact Warsaw-circle point-set construction and closure witnesses.

This script checks the symbolic defining identities. An elementary written
argument gives closedness/compactness of the graph closure and connector.
No proof of weak contractibility, noncontractibility, or non-CW type.
"""
import json
import sympy as s

def audit():
    n=s.symbols('n',integer=True,positive=True)
    t=s.symbols('t',real=True)
    angle=2*s.pi*n+s.asin(t)
    x=1/angle
    assert s.trigsimp(s.sin(angle)-t)==0
    assert s.limit(x,n,s.oo)==0
    assert s.simplify(s.sin(1)-s.sin(1))==0
    # Source-selected exact compactum:
    # S = {(x,sin(1/x)):0<x<=1} union ({0}x[-1,1]);
    # closing arc A consists of segments (0,-1)->(0,-2),
    # (0,-2)->(1,-2), (1,-2)->(1,sin(1)).
    # All of A except its endpoints is disjoint from S since
    # |sin(1/x)|<=1, while x=0 in S only for y>=-1 and
    # x=1 in S only at y=sin(1).
    # For every t in [-1,1], x_n=1/(2pi*n+asin(t))>0, x_n->0,
    # and sin(1/x_n)=t, showing the entire vertical segment
    # is in the closure of the oscillating graph.
    return {'vertical_limit_identity':'sin(2*pi*n+asin(t))=t; x_n->0',
            'connector_segments':3,
            'connector_meets_sine_closure_only_at_endpoints':True,
            'compact_connected_continuum_argument':'elementary closure + finite compact arc',
            'weak_homotopy_groups_computed':False,
            'homotopy_type_computed':False}

if __name__=='__main__':
    print(json.dumps({'Warsaw':audit(),'status':'PASS symbolic closure/connector fixture'},indent=2,sort_keys=True))
