#!/usr/bin/env python3
"""Exact conditional radiation-pressure angular-impulse/torque envelope.

For total source optical power P, radius R, <= B specular or partially
absorbing wall events per photon, and common reflected-power fraction eta
with 0<=eta<=1, each event's wall momentum transfer has norm at most
(1+eta)*P_i/c. The k-th event has P_i<=eta^k*P, so the total signed
torque magnitude cannot exceed:

 |tau_wall| <= (P*R/c)*(1+eta)*sum(eta**k, k=0..B-1).

This is a model bound for ideal rays, NOT a calibration or gravity test.
In particular, it does not bound thermal, mechanical, convection,
electrostatic or other non-optical forces on a real apparatus.
"""
from __future__ import annotations
from fractions import Fraction as Q
import argparse, json

C = 299792458

def envelope(power_watts, radius_metres, max_bounces:int, reflectivity):
    P=Q(str(power_watts))
    R=Q(str(radius_metres))
    eta=Q(str(reflectivity))
    if P<0 or R<0 or type(max_bounces) is not int or max_bounces<0:
        raise ValueError("power, radius and bounce count must be nonnegative")
    if not (0<=eta<=1):
        raise ValueError("reflectivity must lie in [0,1]")
    geometric_sum=sum((eta**k for k in range(max_bounces)),Q(0))
    upper=P*R*(1+eta)*geometric_sum/Q(C)
    perfect_reflector=P*R*(2*max_bounces)/Q(C)
    assert 0<=upper<=perfect_reflector
    return {
        "schema":"radiation_pressure_torque_envelope_v1",
        "optical_power_watts":str(P),
        "max_hit_radius_metres":str(R),
        "max_reflections_per_ray":max_bounces,
        "assumed_reflected_power_fraction_each_hit":str(eta),
        "exact_absolute_wall_torque_bound_Nm":str(upper),
        "absolute_wall_torque_bound_Nm":float(upper),
        "perfect_reflector_bound_Nm":str(perfect_reflector),
        "radiation_pressure_only":True,
        "independent_measurement":False,
        "thermal_electrostatic_mechanical_force_bound":False,
        "assumption":"all emitted optical power enters selected rays and event count is uniformly bounded",
    }

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--watts",default="9000")
    p.add_argument("--radius",default="17/10")
    p.add_argument("--bounces",type=int,default=8)
    p.add_argument("--reflectivity",default="19/20")
    p.add_argument("--output")
    args=p.parse_args()
    result=envelope(args.watts,args.radius,args.bounces,args.reflectivity)
    content=json.dumps(result,indent=2,sort_keys=True)
    if args.output:
        from pathlib import Path
        Path(args.output).write_text(content+"\n")
    print(content)
if __name__=="__main__":main()
