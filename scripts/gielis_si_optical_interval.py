#!/usr/bin/env python3
"""Exact rational SI optical-torque interval under explicit INPUT uncertainty.

Input intervals are *supplied assumptions*, not measurements scraped from
a device. Nonnegative optical power P and hit-radius R with reflectivity
eta in [0,1] and at most B events imply

 |tau| <= P_high R_high (1+eta_high)
          sum(eta_high^k, k=0..B-1) / c.

There is NO positive lower bound for |tau|: signed angular impulses may
cancel, even at nonzero power. This is exact interval propagation under
the ideal radiation-pressure-only hypothesis, with c from the existing
canonical Agda SI carrier.
"""
from __future__ import annotations
from fractions import Fraction as F
import argparse
import json
from gielis_si_owner_adapter import canonical_speed_of_light_si

def si_torque_uncertainty_enclosure(
        power_low_W,power_high_W,
        hit_radius_low_m,hit_radius_high_m,
        reflectivity_low,reflectivity_high,
        bounce_cap:int):
    p0,p1=map(lambda x:F(str(x)),(power_low_W,power_high_W))
    r0,r1=map(lambda x:F(str(x)),(hit_radius_low_m,hit_radius_high_m))
    e0,e1=map(lambda x:F(str(x)),(reflectivity_low,reflectivity_high))
    if not (0<=p0<=p1 and 0<=r0<=r1 and 0<=e0<=e1<=1):
        raise ValueError("positive ordered SI input intervals and 0<=eta<=1 required")
    if type(bounce_cap) is not int or bounce_cap<0:
        raise ValueError("bounce cap must be a nonnegative integer")
    c=canonical_speed_of_light_si()
    factor=(1+e1)*sum((e1**i for i in range(bounce_cap)),F(0))
    torque_bound=p1*r1*factor/F(c)
    ideal_bound=F(2*bounce_cap)*p1*r1/F(c)
    assert 0<=torque_bound<=ideal_bound
    return {
       "source_c_SI_m_per_s":c,
       "source_parameter_type":"user-specified intervals, NOT measured",
       "power_input_W":[str(p0),str(p1)],
       "max_hit_radius_input_m":[str(r0),str(r1)],
       "reflectivity_input":[str(e0),str(e1)],
       "bounce_cap":bounce_cap,
       "absolute_torque_lower_Nm":"0",
       "absolute_torque_upper_Nm":str(torque_bound),
       "signed_torque_interval_Nm":[str(-torque_bound),str(torque_bound)],
       "upper_in_micro_Nm":float(torque_bound*1_000_000),
       "perfect_reflector_upper_Nm":str(ideal_bound),
       "assumptions":"ideal 2D specular/absorbing ray impulse, bounded radius and bounces",
       "role":"wallTorque (N m), not opticalEnergy (J)",
       "lower_bound_cannot_be_promoted_above_zero":True,
       "calibration_receipt_present":False,
       "non_optical_forces_bounded":False,
    }

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--power-low-W",default="8500")
    p.add_argument("--power-high-W",default="9500")
    p.add_argument("--radius-low-m",default="3/2")
    p.add_argument("--radius-high-m",default="17/10")
    p.add_argument("--reflectivity-low",default="9/10")
    p.add_argument("--reflectivity-high",default="19/20")
    p.add_argument("--bounces",type=int,default=8)
    a=p.parse_args()
    print(json.dumps(si_torque_uncertainty_enclosure(
        a.power_low_W,a.power_high_W,a.radius_low_m,a.radius_high_m,
        a.reflectivity_low,a.reflectivity_high,a.bounces),indent=2,sort_keys=True))

if __name__=="__main__":
    main()
