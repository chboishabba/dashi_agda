#!/usr/bin/env python3
"""Exact log-spiral geometric candidate filter; NOT a ray/EM solver.

Attribution: source-written Kozyrev experiment PR #1404; no promotion of
microcavity analogies to Maxwell modes or anomalous torsion.
"""
import math
import json
import argparse

def log_geometry(b, turns, inner=1.5, thickness=.156):
    if not (math.isfinite(b) and 0 <= b <= 2 and
            math.isfinite(turns) and turns > 0 and
            math.isfinite(inner) and inner > 0 and
            math.isfinite(thickness) and thickness >= 0):
        raise ValueError("invalid physical dimensions")
    theta = 2 * math.pi * turns
    outer = inner * math.exp(b * theta)
    previous = inner * math.exp(b * (theta-2*math.pi)) if turns >= 1 else None
    aperture = outer-previous if previous is not None else None
    return dict(family="logarithmic", b=b, turns=turns, inner_m=inner,
                outer_m=outer, pitch_deg=math.degrees(math.atan(b)),
                growth_per_turn_fraction=math.expm1(2*math.pi*b),
                radial_aperture_m=aperture, thickness_m=thickness,
                aperture_open=aperture is not None and aperture>thickness,
                note="necessary radial aperture only: ray geometry remains unverified")

def matched_pitch(inner, outer, turns):
    if inner<=0 or outer<inner or turns<=0:
        raise ValueError("invalid matching radii")
    return math.log(outer/inner)/(2*math.pi*turns)

def audit():
    bs=[0,.005,math.log(1.05)/(2*math.pi),math.log(1.1)/(2*math.pi),
        .03,.05,.1,.15,.2,.3,.5,1]
    turns=[1,1.25,1.5,2,3]
    cases=[log_geometry(b,t) for b in bs for t in turns]
    inner=1.5
    outer=inner+.402*2*math.pi*1.5
    b=matched_pitch(inner,outer,1.5)
    return dict(schema="kozyrev-log-geometry-audit/1", cases=cases,
                reference=dict(archimedean_growth=.402, inner=inner, outer=outer,
                               endpoint_matched_log_b=b,
                               endpoint_matched_log=log_geometry(b,1.5)),
                counts=dict(total=len(cases),
                            open_aperture=sum(c["aperture_open"] for c in cases)),
                limit="No ray-traced focusing, torque, directional force or residence claims")

if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--output")
    args=parser.parse_args()
    result=json.dumps(audit(),indent=2)
    if args.output:
        with open(args.output,"w",encoding="utf-8") as f:f.write(result+"\n")
    else:print(result)
