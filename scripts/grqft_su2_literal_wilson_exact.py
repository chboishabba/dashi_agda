#!/usr/bin/env python3
"""Exact SU(2) quaternion evaluation of one genuine Wilson matrix plaquette.

In the fundamental SU(2) representation Re Tr(U)=2*scalar(U). The
positive Wilson cost is 1-ReTr(U)/2. For conventional bare beta=4/g0²,
S_W=4*g0^{-2} * cost. Links are exact rational unit quaternions.

This producer does NOT evaluate CMP119 E/R/B/vacuum sectors, an SU(2)
Haar integral, finite-volume Gibbs normalization, an RG beta function,
a metric derivative, or a renormalized continuum quantum stress.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path

def fraction(x):
    if isinstance(x, bool) or not isinstance(x, (str, int)):
        raise ValueError("exact rational scalar required")
    return F(x)

def quat(raw):
    if not isinstance(raw, list) or len(raw) != 4:
        raise ValueError("SU2 link must contain four rational components")
    q = tuple(fraction(x) for x in raw)
    if sum((x*x for x in q), F(0)) != 1:
        raise ValueError("SU2 quaternion must have norm exactly one")
    return q

def multiply(a, b):
    w,x,y,z = a
    p,q,r,s = b
    return (w*p-x*q-y*r-z*s,
            w*q+x*p+y*s-z*r,
            w*r-x*s+y*p+z*q,
            w*s+x*r-y*q+z*p)

def inverse(a):
    w,x,y,z = a
    return (w,-x,-y,-z)

def loop(links):
    # Oriented boundary A->B->C->D->A. All links A B, B C,
    # D C, A D are supplied in the positive edge orientation.
    ab,bc,dc,ad = links
    return multiply(multiply(multiply(ab,bc),inverse(dc)),inverse(ad))

def gauge(links, transforms):
    ab,bc,dc,ad = links
    a,b,c,d = transforms
    return [multiply(multiply(a,ab),inverse(b)),
            multiply(multiply(b,bc),inverse(c)),
            multiply(multiply(d,dc),inverse(c)),
            multiply(multiply(a,ad),inverse(d))]

def evaluate(source):
    if not isinstance(source, dict):
        raise ValueError("source must be a JSON object")
    provenance = source.get("provenance")
    if not isinstance(provenance, dict):
        raise ValueError("source revision/cutoff provenance missing")
    for field in ("source_id","revision","cutoff","link_frame"):
        if not isinstance(provenance.get(field),str) or not provenance[field]:
            raise ValueError(f"missing provenance: {field}")
    try:
        links = [quat(source["links"][x]) for x in ("AB","BC","DC","AD")]
        u = fraction(source["inverse_bare_coupling_square"])
    except (KeyError,TypeError) as exc:
        raise ValueError("invalid selected link/coupling input") from exc
    if u <= 0:
        raise ValueError("positive inverse bare coupling square required")
    holonomy = loop(links)
    trace = 2*holonomy[0]
    cost = 1 - trace/F(2)
    if cost < 0 or cost > 2:
        raise ArithmeticError("unit quaternion Wilson cost outside [0,2]")
    action = 4*u*cost
    out = {
        "status":"single_exact_SU2_matrix_plaquette_only",
        "provenance":provenance,
        "holonomy":[str(x) for x in holonomy],
        "real_trace":str(trace),
        "cost_1_minus_half_trace":str(cost),
        "beta_bare_SU2":str(4*u),
        "bare_wilson_action":str(action),
        "negative_cost":str(-cost),
        "negative_orientation_coefficient":str(-4*u),
        "negative_oriented_action":str((-4*u)*(-cost)),
        "unit_coefficient_basis_value":str(4*cost),
        "unit_coefficient_action":str(u*(4*cost)),
        "same_action_orientation":action==(-4*u)*(-cost)==u*(4*cost),
        "physical_CMP119_effective_action_identified":False,
        "Haar_measure_or_continuum_constructed":False
    }
    if "vertex_gauge" in source:
        g = [quat(source["vertex_gauge"][x]) for x in ("A","B","C","D")]
        transformed = loop(gauge(links,g))
        if transformed[0]!=holonomy[0]:
            raise ArithmeticError("rational SU2 gauge-invariance check failed")
        out["gauge_transformed_real_trace"] = str(2*transformed[0])
        out["gauge_trace_invariant"] = True
    return out

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("source",type=Path)
    p.add_argument("--out",type=Path)
    args=p.parse_args()
    raw=args.source.read_bytes()
    result=evaluate(json.loads(raw))
    result["input_sha256"]=hashlib.sha256(raw).hexdigest()
    text=json.dumps(result,sort_keys=True,indent=2)+"\n"
    if args.out: args.out.write_text(text)
    else: print(text,end="")

if __name__=="__main__":
    main()
