#!/usr/bin/env python3
"""Exact overlap-point witnesses for the REAL C3 radius-cover API.

Reuses existing literal source owners, not a copy of their geometry:
  alexander_horned_c3_explicit_open_cover.{CENTRES,RIN,ROUT,d2}
  alexander_horned_c3_equivariant_basing_paths.{X0,C,P,rotate}

Lean consumer:
  ThreeArmRadiusConnectedAssembly.radiusArms_meet_of_points
  and IsPathConnected.union (Mathlib).
The source scripts certify *ambient coordinates*, not that the wild
exterior inclusion or member path-connectedness was kernel instantiated.
"""
from fractions import Fraction as F
from alexander_horned_c3_explicit_open_cover import CENTRES,RIN,ROUT,d2,exact_certificate
from alexander_horned_c3_equivariant_basing_paths import X0,C,P,rotate

def core(x, inner=RIN):
    return all(d2(x,c)>inner*inner for c in CENTRES)

def satellite_arm(x,i,outer=ROUT):
    return d2(x,CENTRES[i])<outer*outer

def outside_allowed_solids(x):
    # This is a sufficient envelope test: the real wild B_i is inside
    # a unit ball about its centre. The central ball radius=1 and
    # three straight spoke tubes have axis t in [1/2,17/2].
    if d2(x,(F(0),)*3)<=1:
        return False
    if any(d2(x,c)<=1 for c in CENTRES):
        return False
    for i in range(3):
        if F(1,2)<=x[i]<=F(17,2) and sum(
          x[j]*x[j] for j in range(3) if j!=i)<=F(1,16):
            return False
    return True

def audit():
    assert C==CENTRES
    assert RIN==F(15,4) and ROUT==F(17,4)
    exact_certificate()             # pre-existing cover inequalities
    assert rotate(X0)==X0 and core(X0)
    for i in range(3):
        p=P[i]
        assert p[i]==13 and all(p[j]==0 for j in range(3) if j!=i)
        assert d2(p,CENTRES[i])==16
        assert all(d2(p,CENTRES[j])==250 for j in range(3) if j!=i)
        assert core(p) and satellite_arm(p,i)
        assert outside_allowed_solids(p)
        assert all(not satellite_arm(p,j) for j in range(3) if j!=i)
        assert rotate(p)==P[(i+1)%3]
        # Two severe controls: a point too close to the satellite
        # fails the central inner cut; too far fails the outer arm.
        inner_bad=tuple(F(12) if j==i else F(0) for j in range(3))
        outer_bad=tuple(F(14) if j==i else F(0) for j in range(3))
        assert not core(inner_bad)
        assert not satellite_arm(outer_bad,i)
    # Each actual p_i is a literal point in C∩S_i for the
    # source-supported geometry; it is NOT by itself a proof that
    # S_i or U_i is path-connected.
    return {
      'status':'PASS', 'overlap_points':[list(map(str,p)) for p in P],
      'dist2_own':16,'dist2_foreign':250,
      'central_basepoint_clearance':921,
      'radius_cut':(str(RIN),str(ROUT)),
      'negative_controls':'PASS (inner exclusion; outer miss)',
      'source_satellite_connected':False,
      'central_pi1_kernel_proved':False,
      'wild_same_object_embedding_kernel_proved':False
    }

if __name__=='__main__':
    import json
    print(json.dumps(audit(),indent=2))
