#!/usr/bin/env python3
"""Independent continuous-ray vs polyline first-hit parity for the NEW scene.

The continuous solver roots cross(X(theta)-origin,d)=0 with Brent
bracketing directly on the analytic log-modulated spiral. The polyline
solver is the independently implemented segment intersection in the
existing experiment. Sign-change bracketing may miss exact grazing
tangencies; the report excludes those from transversality claims.
This DOES NOT claim parity with the original Kozyrev HTML SDF apparatus.
"""
from __future__ import annotations
import argparse, json, math
import numpy as np
from scipy.optimize import brentq
import gielis_base369_experiments as Exp

TURN=3*math.pi
START=np.array([1.05,0.],dtype=float)

def smooth_curve(theta,m,eps):
    t=np.asarray(theta)
    h=lambda a: -.5*np.log((3+eps*np.cos(m*a))/3)
    hh=h(t)-h(0.)-(h(TURN)-h(0.))*t/TURN
    r=np.exp(math.log(.75)+math.log(1.55/.75)*t/TURN+hh)
    return np.stack((r*np.cos(t),r*np.sin(t)),axis=-1)

def smooth_tangent(theta,m,eps):
    rvec=smooth_curve(theta,m,eps)
    r=np.linalg.norm(rvec,axis=-1)
    hprime=eps*m*np.sin(m*np.asarray(theta))/(2*(3+eps*np.cos(m*np.asarray(theta))))
    hdelta=(-.5*math.log((3+eps*math.cos(m*TURN))/3)
            +.5*math.log((3+eps)/3))/TURN
    dr=r*(math.log(1.55/.75)/TURN+hprime-hdelta)
    t=np.asarray(theta)
    return np.stack((dr*np.cos(t)-r*np.sin(t),dr*np.sin(t)+r*np.cos(t)),axis=-1)

def continuous_first_hit(angle,m,eps,brackets=6144):
    direction=np.array([math.cos(angle),math.sin(angle)])
    grid=np.linspace(0,TURN,brackets+1)
    points=smooth_curve(grid,m,eps)
    value=Exp.cross(points-START,direction)
    roots=[]
    for i in np.nonzero((value[:-1]*value[1:]<0)|(value[:-1]==0))[0]:
        left,right=float(grid[i]),float(grid[i+1])
        def residual(t):
            return float(Exp.cross(smooth_curve(t,m,eps)-START,direction))
        root=left if abs(residual(left))<1e-12 else brentq(
            residual,left,right,xtol=1e-13)
        p=smooth_curve(root,m,eps)
        t=float(np.dot(p-START,direction))
        if t>1e-7:
            tangent=smooth_tangent(root,m,eps)
            trans=abs(float(Exp.cross(tangent,direction)))/float(
                np.linalg.norm(tangent))
            roots.append((t,p,trans,root))
    if not roots:return None
    return min(roots,key=lambda h:h[0])

def parity(m=3,epsilon=.12,rays=48,segments=1536,brackets=6144,
           minimum_transversality=.05):
    boundary=Exp.spiral_vertices(m,epsilon,segments)
    results=[]
    for j in range(rays):
        angle=2*math.pi*(j+.319)/rays
        d=np.array([math.cos(angle),math.sin(angle)])
        poly=Exp.nearest_hit(START,d,boundary)
        analytic=continuous_first_hit(angle,m,epsilon,brackets)
        if poly is None and analytic is None:
            continue
        if poly is None or analytic is None:
            results.append({"ray":j,"status":"unpaired_first_hit"})
            continue
        at,ap,trans,theta=analytic
        pt,pp,normal,segment=poly
        dist=float(np.linalg.norm(ap-pp))
        results.append({
          "ray":j,"status":"paired","continuous_t":at,"polyline_t":pt,
          "first_hit_discrepancy_m":dist,
          "transversality":trans,
          "nongrazing":trans>=minimum_transversality,
          "theta":theta,"segment":segment,
        })
    paired=[x for x in results if x["status"]=="paired"]
    nongrazing=[x for x in paired if x["nongrazing"]]
    return {
       "geometry":"new endpoint-locked analytic log-Gielis spiral",
       "same_as_original_Kozyrev_HTML_SDF":False,
       "m":m,"epsilon":epsilon,"rays":rays,"segments":segments,
       "bracketing_nodes":brackets,
       "paired":len(paired),
       "unpaired":sum(x["status"]=="unpaired_first_hit" for x in results),
       "nongrazing_paired":len(nongrazing),
       "max_first_hit_error_m":max((x["first_hit_discrepancy_m"] for x in paired),
                                   default=None),
       "max_nongrazing_error_m":max(
           (x["first_hit_discrepancy_m"] for x in nongrazing),default=None),
       "grazing_and_tangency_completeness_proved":False,
       "original_HTML_SDF_crossover_proved":False,
       "first_hits":results,
    }

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--m",type=int,default=3)
    p.add_argument("--epsilon",type=float,default=.12)
    p.add_argument("--rays",type=int,default=48)
    p.add_argument("--segments",type=int,default=1536)
    p.add_argument("--brackets",type=int,default=6144)
    p.add_argument("--output")
    a=p.parse_args()
    out=parity(a.m,a.epsilon,a.rays,a.segments,a.brackets)
    payload=json.dumps(out,indent=2)
    if a.output:
        from pathlib import Path
        Path(a.output).write_text(payload+"\n")
    print(payload)
if __name__=="__main__":main()
