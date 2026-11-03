#!/usr/bin/env python3
"""Explicit optical-loop consistency, not a global 4D quantum fermion fixed point.

Reuses the committed finite-tower EFFECTIVE BVP replay. A specified closed
magnetic field-line CFT requires L_opt = tau_inside + tau_return. The external
return is a positive prescribed optical distance, not solved Maxwell field
lines, exterior fermionic stress or coupled 4D geometry.
"""
from scipy.optimize import brentq
from check_mmp_global_effective_bvp_replay_20261024 import run

def mismatch(L,q=12,return_optical=2.):
    d=run(q,L=L)
    return L-d['interior_radial_lighttime']-return_optical,d

def main():
    for q in (10,11,12,13,24):
        mis,d=mismatch(20.,q=q)
        print('L=20 q',q,'inside',round(d['interior_radial_lighttime'],6),
              'budget',round(mis+2,6))
        assert (mis+2<0)==(q in (12,13,24))
    L=brentq(lambda L:mismatch(L)[0],20,26,xtol=1e-8)
    residual,d=mismatch(L)
    assert abs(residual)<1e-7
    assert d['radial_ANEC']<0 and abs(d['Ktt_jump'])<1e-8
    assert abs(L-22.516301125725)<0.005
    print('PASS conditional L fixed point',L,'inside',d['interior_radial_lighttime'],
          'RN_R',d['match_radius'],'RN_M',d['mass_RN'],'ANEC',d['radial_ANEC'])
    print('OPEN: actual closed external field-line geometry and same quantum state/stress on return path')
if __name__=='__main__':main()
