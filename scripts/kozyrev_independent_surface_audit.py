#!/usr/bin/env python3
"""Independent continuous-spiral surface proximity audit for HTML event receipts.

Unlike the HTML SDF 3-step Gauss-Newton, this referee uses bounded
scalar minimisation over independent angular subintervals.
A hit within contact tolerance is necessary, NOT sufficient, for
correct earliest ray/physical wall intersection.
Source-written Kozyrev PR #1404; scipy required.
"""
import argparse
import json
import math
import numpy as np
from scipy.optimize import minimize_scalar

def closest(scene, position):
    g=scene["geometry"]
    inner=g["inner"]
    growth=g["growth"]
    turns=g["turns"]
    length=2*math.pi*turns
    rotation=math.radians(g["srot"])
    family=g.get("family","arch")
    correction=g.get("correction",0)
    half=g["thick"]/2
    def distance_sq(t):
        r=(inner*math.exp(growth*t) if family=="log"
           else inner+growth*t+(correction*math.sin(t/turns)
                                if family=="segmented" else 0))
        theta=t+rotation
        return (r*math.cos(theta)-position[0])**2+(r*math.sin(theta)-position[1])**2
    cuts=np.linspace(0,length,max(16,math.ceil(turns*20))+1)
    minimum=min(distance_sq(0.),distance_sq(length))
    best=0.
    for a,b in zip(cuts[:-1],cuts[1:]):
        result=minimize_scalar(distance_sq,bounds=(a,b),method="bounded",
                               options={"xatol":1e-12})
        if result.fun<minimum:
            minimum=result.fun
            best=result.x
    return math.sqrt(max(0,minimum))-half,best

def audit(data, max_per_ray=4, tolerance=.0007):
    rows=[]
    for ray in data["rays"]:
        hits=ray["hits"]
        indices=set(range(min(2,len(hits))))
        if hits:
            indices.add(len(hits)//2)
            indices.add(len(hits)-1)
        for index in sorted(indices):
            dist,t=closest(data["scene"],hits[index]["point"])
            rows.append({"ray":ray["id"],"index":index,
                         "surface_signed_distance_m":dist,"parameter_t":t})
    absolute=[abs(x["surface_signed_distance_m"]) for x in rows]
    return {"schema":"kozyrev-independent-surface-check/1",
            "samples":len(rows),
            "median_absolute_error_m":float(np.median(absolute)),
            "max_absolute_error_m":max(absolute),
            "outside_tolerance":sum(x>tolerance for x in absolute),
            "tolerance_m":tolerance,
            "scope":"Surface proximity only, not earliest-forward-intersection certification",
            "details":rows}

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("events")
    p.add_argument("--output")
    args=p.parse_args()
    with open(args.events,encoding="utf-8") as f: result=audit(json.load(f))
    output=json.dumps(result,indent=2)
    if args.output:
        with open(args.output,"w",encoding="utf-8") as f:f.write(output+"\n")
    else:print(output)
