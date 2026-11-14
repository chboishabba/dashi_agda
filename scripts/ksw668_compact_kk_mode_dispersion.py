#!/usr/bin/env python3
"""Negative control: compact spacelike product-KK mass tower does NOT give FTL.

ds5²=-dt²+dx²+du²+dv²+R²dy², y periodic. A 5D massless scalar
plane wave with integer KK mode n obeys omega²=k²+n²/R².
For k>=0: v_group=k/sqrt(k²+n²/R²)<=1, with equality n=0.
This is a flat product-KK theorem only; it does NOT forbid shortcuts
from a curved brane's extrinsic geometry or dynamical braneworld.
No observed KK mode, SUSY vacuum-energy cancellation, string-UV
identification or bulk source/detector coupling follows.
"""
import sympy as s
import json

def audit():
    k,R,n=s.symbols("k R n",positive=True)
    omega=s.sqrt(k*k+n*n/R**2)
    group=s.simplify(s.diff(omega,k))
    gap=s.simplify(1-group**2)
    assert s.simplify(gap-n*n/(R**2*k**2+n**2))==0
    assert s.simplify(group.subs({k:3,n:1,R:1})-3/s.sqrt(10))==0
    assert s.simplify(omega.subs({k:3,n:1,R:1})**2-10)==0
    return {
      "status":"PASS exact subluminal positive-KK-mode group-velocity identity",
      "geometry":"5D flat product x spacelike S1",
      "omega_squared":"k²+n²/R²",
      "four_D_effective_mass_squared":"n²/R²",
      "group_velocity":str(group),
      "positive_one_minus_group_velocity_squared":str(gap),
      "n1_R1_k3_group_velocity":float(3/s.sqrt(10)),
      "zero_mode_group_velocity":1,
      "product_compact_KK_alone_shortcut":False,
      "curved_brane_shortcut_excluded":False,
      "winding_scalar_brane_is_not_KK_mass_tower":True,
      "SUSY_or_string_identification_proven":False,
      "physical_graviton_source_receiver_coupled":False
    }

if __name__=="__main__":
    print(json.dumps(audit(),sort_keys=True,indent=2))
