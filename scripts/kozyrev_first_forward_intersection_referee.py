#!/usr/bin/env python3
"""Independent polyline ray/offset-spiral first-impact referee.

This is independent of SDF nearest-point search. Discretisation remains an
approximation and must be checked by doubling samples. Original computation
by Kozyrev PR #1404; optical geometry and torque theory are inherited.
"""
import json, math, argparse
import numpy as np

def surfaces(g, samples=25000):
    theta=np.linspace(0,2*math.pi*g["turns"],samples+1)
    growth=g["growth"]; inner=g["inner"]; turns=g["turns"]
    fam=g.get("family","arch")
    if fam=="log":
        r=inner*np.exp(growth*theta); dr=growth*r
    elif fam=="segmented":
        corr=g.get("correction",0.)
        r=inner+growth*theta+corr*np.sin(theta/turns)
        dr=growth+corr*np.cos(theta/turns)/turns
    else:
        r=inner+growth*theta
        dr=np.full_like(theta,growth)
    a=theta+math.radians(g["srot"])
    ca=np.cos(a);sa=np.sin(a)
    x=r*ca;y=r*sa
    tx=dr*ca-r*sa;ty=dr*sa+r*ca
    norm=np.hypot(tx,ty)
    nx=-ty/norm;ny=tx/norm
    w=g["thick"]/2
    sides=[np.column_stack((x+w*nx,y+w*ny)),
           np.column_stack((x-w*nx,y-w*ny))]
    segs=[(side[:-1],side[1:]) for side in sides]
    for index in (0,-1):
        segs.append((np.array([sides[0][index]]),
                     np.array([sides[1][index]])))
    return segs

def first_cross(segments, origin, direction, epsilon=0.003):
    ox,oy=origin;dx,dy=direction
    minimum=math.inf
    for a,b in segments:
        ex=b[:,0]-a[:,0]; ey=b[:,1]-a[:,1]
        den=dx*ey-dy*ex
        nz=np.abs(den)>1e-12
        px=a[:,0]-ox;py=a[:,1]-oy
        t=np.full(len(a),math.inf);u=np.full(len(a),math.inf)
        np.divide(px*ey-py*ex,den,out=t,where=nz)
        np.divide(px*dy-py*dx,den,out=u,where=nz)
        hit=nz&(t>epsilon)&(u>=0)&(u<=1)
        if np.any(hit):minimum=min(minimum,float(np.min(t[hit])))
    return minimum

def audit(receipt, samples=25000):
    segments=surfaces(receipt["scene"]["geometry"],samples)
    differences=[]
    missed=0
    for ray in receipt["rays"]:
        if not ray["hits"]:continue
        source=ray["source"]
        independent=first_cross(segments,source["point"],source["direction"])
        if not math.isfinite(independent):
            missed+=1
            continue
        observed=math.dist(source["point"],ray["hits"][0]["point"])
        differences.append(independent-observed)
    a=np.asarray(differences)
    return dict(inspected=len(differences)+missed,finite=len(differences),
                missed=missed,median_signed_m=float(np.median(a)) if len(a) else None,
                max_abs_m=float(np.max(np.abs(a))) if len(a) else None,
                signed_range_m=[float(np.min(a)),float(np.max(a))] if len(a) else None,
                samples=samples,
                scope="FIRST collision only, polygonal finite-thickness boundary; not validated subsequent reflections")
if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("receipts",nargs="+")
    p.add_argument("--samples",type=int,default=25000)
    args=p.parse_args()
    print(json.dumps([dict(file=f,**audit(json.load(open(f)),args.samples))
                      for f in args.receipts],indent=2))
