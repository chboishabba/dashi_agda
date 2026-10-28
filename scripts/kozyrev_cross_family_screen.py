#!/usr/bin/env python3
"""Finite-panel cross-family *screen*, not the HTML SDF or a Maxwell solver.

Source-written in Kozyrev PR #1404. Existing spiral and torque results retain
theirs; categorical 3^3 and S3 experiments are indexing, not causal physics.
"""
from __future__ import annotations
import itertools
import json
import math
from kozyrev_geometry_optimizer import vertices, first_hit, dot, cross, sub, scale, add

C = 299792458.0
AXES = ("capture", "clockwise_wall_torque", "residence")
TRITS = (-1, 0, 1)

def categorical_27():
    """27 discrete settings of three distinct experimental *factors*."""
    return list(itertools.product(TRITS, repeat=3))

def s3_objective_permutations():
    """Six orderings of the objectives; do not confuse priorities with forces."""
    return list(itertools.permutations(AXES))

def geometry_family(name, turns, inner, outer, *, correction=0., panels=400):
    """Reuse the pre-existing parametrised geometry and intersection."""
    if name == "arch":
        k = 0.
    elif name == "log":
        k = math.log(outer / inner)
    elif name == "segmented":
        k = 0.
    else:
        raise ValueError("unknown geometry family")
    return vertices(k, correction, panels=panels, turns=turns,
                    inner_radius=inner, outer_radius=outer)

def trace(points, source, direction, *, power=9000., rho=.95,
          target_on=True, target=(0.,0.), radius=.1, max_bounces=80):
    """Zero-thickness polygonal multi-hit fixture; one directional ray.

    Distinct from HTML SDF with solid finite-thickness walls. This
    screening tracer does not enforce an exterior entrance gate.
    """
    p = tuple(source)
    d = tuple(direction)
    weight=power
    wall_torque=0.
    wall_heat=0.
    target_power=0.
    escape_power=0.
    unresolved_power=0.
    dwell=0.
    hits=0
    for n in range(max_bounces+1):
        h=first_hit(p,d,points,epsilon=1e-7)
        wall_distance=h[0] if h else math.inf
        target_distance=math.inf
        if target_on:
            ox,oy=sub(p,target)
            proj=ox*d[0]+oy*d[1]
            delta=proj*proj-(ox*ox+oy*oy-radius*radius)
            if delta>=0:
                z=-proj-math.sqrt(delta)
                if z>1e-7:
                    target_distance=z
        if target_distance<wall_distance:
            dwell+=weight*target_distance/C
            target_power+=weight
            break
        if h is None:
            escape_power+=weight
            break
        if n==max_bounces:
            unresolved_power+=weight
            break
        t,point,tangent=h
        dwell+=weight*t/C
        outgoing=sub(scale(2*dot(d,tangent)/dot(tangent,tangent),tangent),d)
        outpower=weight*rho
        momentum=sub(scale(weight/C,d),scale(outpower/C,outgoing))
        wall_torque+=cross(point,momentum)
        wall_heat+=weight-outpower
        hits+=1
        p=add(point,scale(1e-7,outgoing))
        d=outgoing
        weight=outpower
    return dict(wall_torque_Nm=wall_torque,target_W=target_power,
                escape_W=escape_power,unresolved_W=unresolved_power,
                wall_heat_W=wall_heat,reflections=hits,
                dwell_ns=dwell/power*1e9)

def screen():
    inner,outer=1.5,1.5+.402*2*math.pi*1.5
    source=(2.5,0.)
    rows=[]
    # Different name families share source and endpoint radii. The model
    # does NOT match the user's inlet-aperture boundary conditions.
    for family in ("arch","log","segmented"):
        for turns in (1.,1.5,2.):
            for corr in ((-.035,0.,.035) if family=="segmented" else (0.,)):
                pts=geometry_family(family,turns,inner,outer,correction=corr)
                if pts is None: continue
                for absorber in (False,True):
                    for handedness in (-1,1):
                        # Exact planar mirror x-axis parity by reflecting y.
                        wall=pts if handedness==1 else [(x,-y) for x,y in pts]
                        direction=(math.cos(.51*math.pi),handedness*math.sin(.51*math.pi))
                        row=trace(wall,source,direction,target_on=absorber)
                        rows.append(dict(family=family,turns=turns,
                                         correction=corr,handedness=handedness,
                                         absorber_on=absorber,**row))
    return dict(schema="kozyrev-cross-family-screen/1",
                comparisons=rows,
                categorical_27_count=len(categorical_27()),
                s3_priority_orderings=len(s3_objective_permutations()),
                test_boundary="zero-thickness finite-panel 2D *internal-source* fixture; no physical optimum, no ray SDF agreement")

if __name__ == "__main__":
    print(json.dumps(screen(),indent=2))
