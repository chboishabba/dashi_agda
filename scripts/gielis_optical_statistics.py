#!/usr/bin/env python3
"""Matched random-angle optical uncertainty bounds, not apparatus calibration.

Given IID uniform ray directions, each source ray shares equal power and
is traced with a fixed finite bounce budget. Hoeffding intervals cover the
true directional means; a union bound provides simultaneous coverage for
both focus and mean absolute wall angular impulse across all designs.
Pseudorandom seeds make the computational experiment reproducible, not
independently measured. Deterministic equally spaced rays DO NOT justify
these confidence intervals.
"""
from __future__ import annotations
import argparse, json, math
import numpy as np
import gielis_base369_experiments as Exp

def hoeffding(values,lo,hi,alpha):
    n=len(values)
    if n<=0 or hi<lo or not (0<alpha<1):
        raise ValueError("nonempty IID sample, bounded range and alpha needed")
    mean=float(sum(values)/n)
    if not (lo-1e-9<=mean<=hi+1e-9):
        raise ValueError("observable leaves certified range")
    radius=(hi-lo)*math.sqrt(math.log(2/alpha)/(2*n))
    return [max(lo,mean-radius),min(hi,mean+radius)]

def matched_random_sweep(rays=720,segments=1536,bounces=8,
                         seed=369,confidence=.95,include_controls=True):
    if rays<=0 or segments<100 or bounces<0 or not (0<confidence<1):
        raise ValueError("invalid experiment parameters")
    designs=[(3,0.),(3,.12),(3,.24),(6,.12),(6,.24),(9,.12),(9,.24)]
    if include_controls:
        designs.extend([(4,.12),(4,.24),(5,.12),(5,.24),(7,.12),(7,.24)])
    # Common random directions for paired controlled comparison.
    theta=np.random.default_rng(seed).uniform(0,2*math.pi,size=rays)
    alpha_each=(1-confidence)/(2*len(designs))
    # Each wall impulse magnitude <= 2 * 1.70m, and <= B reflections/ray.
    max_abs_impulse=2*1.70*bounces
    output=[]
    for m,epsilon in designs:
        boundary=Exp.spiral_vertices(m,epsilon,segments)
        traced=[Exp.trace_ray(float(a),boundary,max_bounces=bounces)
                for a in theta]
        focus=[int(t["hit_target"]) for t in traced]
        impulse=[float(t["absolute_torque"]) for t in traced]
        signed=[float(t["signed_torque"]) for t in traced]
        if any(x>max_abs_impulse+1e-8 for x in impulse):
            raise AssertionError("wall angular impulse exceeds declared range")
        output.append({
            "m":m,"epsilon":epsilon,
            "rays":rays,"seed":seed,
            "focus_fraction":sum(focus)/rays,
            "mean_abs_torque":sum(impulse)/rays,
            "mean_signed_torque":sum(signed)/rays,
            "focus_hoeffding_interval":hoeffding(focus,0,1,alpha_each),
            "mean_abs_impulse_hoeffding_interval":
                hoeffding(impulse,0,max_abs_impulse,alpha_each),
            "angle_source":"IID uniform directions, pseudo-random sample",
            "physical_calibration":False,
        })
    return {
       "model":"ideal 2D specular ray trace, matched IID source angles",
       "familywise_simultaneous_coverage_at_least":confidence,
       "statistical_condition":"independent uniform random source angles, fixed scene",
       "no_inference_for_deterministic_grid":True,
       "no_fabrication_or_power_measurement":True,
       "alpha_each":alpha_each,
       "max_absolute_angular_impulse_m_per_ray":max_abs_impulse,
       "results":output,
       "pareto_min_impulse":Exp.pareto(output,"min"),
       "pareto_max_impulse":Exp.pareto(output,"max"),
    }

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--rays",type=int,default=720)
    p.add_argument("--segments",type=int,default=1536)
    p.add_argument("--bounces",type=int,default=8)
    p.add_argument("--seed",type=int,default=369)
    p.add_argument("--confidence",type=float,default=.95)
    p.add_argument("--output")
    args=p.parse_args()
    output=matched_random_sweep(args.rays,args.segments,args.bounces,
                                args.seed,args.confidence)
    text=json.dumps(output,indent=2)
    if args.output:
        from pathlib import Path
        Path(args.output).write_text(text+"\n")
    print(text)

if __name__=="__main__":main()
