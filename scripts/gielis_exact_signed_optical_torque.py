#!/usr/bin/env python3
"""Exact selected SI signed optical ray torque; reusable original Hodge sign.

The wall receives P/c*(d_in-eta*d_out), so the planar z-torque is
 (P/c)*(x*(in_y-eta*out_y)-y*(in_x-eta*out_x)) [N m].

All user-supplied P, r, directions, eta are exact rational model
parameters, NOT measured optical transfer or validated normals.
"""
from __future__ import annotations
from fractions import Fraction as F
import json
from gielis_si_owner_adapter import canonical_speed_of_light_si

def signed_lever(x,y,inx,iny,outx,outy,eta):
    x,y,inx,iny,outx,outy,eta=map(lambda v:F(str(v)),
                                  (x,y,inx,iny,outx,outy,eta))
    if not 0<=eta<=1:raise ValueError("reflectivity in [0,1] required")
    return x*(iny-eta*outy)-y*(inx-eta*outx)

def torque_event(power_W,x,y,inx,iny,outx,outy,eta):
    p=F(str(power_W))
    if p<0:raise ValueError("nonnegative input optical power required")
    lever=signed_lever(x,y,inx,iny,outx,outy,eta)
    torque=p*lever/F(canonical_speed_of_light_si())
    return {
      "source_c_SI_m_per_s":canonical_speed_of_light_si(),
      "exact_signed_lever_m":str(lever),
      "exact_signed_torque_Nm":str(torque),
      "signed_torque_micro_Nm":float(torque*1000000),
      "unit":"N m (torque), not J",
      "right_hand_rule":"positive z = x Fy - y Fx",
      "same_watts_and_geometry_are_assumed":True,
      "empirical_calibration_present":False,
    }

def receipt():
    p=F(9000)
    pos=(F(1),F(0))
    plus=torque_event(p,*pos,0,1,0,-1,1)
    minus=torque_event(p,*pos,0,-1,0,1,1)
    zero=torque_event(p,*pos,1,0,-1,0,1)
    assert F(plus["exact_signed_torque_Nm"]) == 2*p/F(canonical_speed_of_light_si())
    assert F(minus["exact_signed_torque_Nm"]) == -F(plus["exact_signed_torque_Nm"])
    assert F(zero["exact_signed_torque_Nm"]) == 0
    rotated=torque_event(p,-1,0,0,-1,0,1,1)
    assert rotated["exact_signed_torque_Nm"]==plus["exact_signed_torque_Nm"]
    return {
        "status":"exact_SI_signed_angular_impulse_event_passed",
        "positive_torque":plus,
        "negative_torque":minus,
        "zero_torque":zero,
        "rotation_pi_invariant":True,
        "interchange_in_out_negative_when_reflectivity_one":True,
        "actual_power_or_hit_measurement":False,
        "native_Agda_kernel_accepted":False,
    }

if __name__=="__main__":
    print(json.dumps(receipt(),indent=2,sort_keys=True))
