#!/usr/bin/env python3
"""10 m2 solar input benchmark and two-score ray screen.

Uses canonical kozyrev_geometry_optimizer first-hit/collision methods.
Synthetic 2D geometry, not full wave optics, physical thrust, or a human-safe concentrator.
"""
import json
from math import pi,cos,sin
import kozyrev_geometry_optimizer as G

C=299792458.0

def solar(area=10.0, insolation=1000.0, optical_efficiency=0.90,
          absorbed_fraction=0.05, lever_arm=0.5):
    assert area>=0 and insolation>=0 and lever_arm>=0
    assert 0<=optical_efficiency<=1 and 0<=absorbed_fraction<=1
    incoming=area*insolation
    transmitted=incoming*optical_efficiency
    return dict(area_m2=area, irradiance_W_m2=insolation,
        collected_W=incoming, delivered_W=transmitted,
        local_absorption_W=transmitted*absorbed_fraction,
        incident_momentum_flux_N=incoming/C,
        entrance_momentum_flux_N=transmitted/C,
        full_reversal_force_ceiling_N=2*incoming/C,
        ideal_surface_torque_scale_Nm=2*transmitted*lever_arm/C,
        caveat="ceilings for directed photon momentum, not force accumulated per bounce; supports/lens and radiation-out must be included")

def first_bounce_scores(points, source=(2.5,0.0), angles=None, target=(0.0,0.0), radius=.1):
    if angles is None: angles=[pi-0.04,pi,pi+0.04]
    readings=[]
    for a in angles:
        ray=(cos(a),sin(a))
        data=G.bounce(source,ray,points,target,radius)
        if data is not None:
            readings.append(data)
    return dict(n_input=len(angles), n_wall_hits=len(readings),
        focus_fraction=sum(int(v['capture']) for v in readings)/len(angles),
        mean_wall_angular_impulse=sum(v['torque'] for v in readings)/len(angles),
        first_bounce_only=True)

def screen():
    rows=[]
    for k in (-4,-2,0,1,2,4):
        vertices=G.vertices(k,panels=9,turns=1.5,
          inner_radius=.75,outer_radius=1.55)
        s=first_bounce_scores(vertices)
        rows.append(dict(k=k,**s))
    return rows

if __name__=="__main__":
    print(json.dumps(dict(solar=solar(),first_bounce_screen=screen(),
       next_gate="complete paths, include source/lens recoil, thermal radiation, wave/metal response, safety; no physical experiment"),indent=2))
