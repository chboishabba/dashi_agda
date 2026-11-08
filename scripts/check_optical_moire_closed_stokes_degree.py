#!/usr/bin/env python3
"""Finite geodesic triangulation of a compactified Jones/Stokes map.
Synthetic validation only; original optical moire research is Dev & Shen
(2026), DOI 10.1038/s41377-026-02533-w.
Requires a constant Stokes boundary and no invalid or ambiguous triangles.
The result is numerical, not interval-certified real arithmetic.
"""
import json
import numpy as np

def solid_angle(a,b,c):
    numer=np.sum(a*np.cross(b,c,axis=0),axis=0)
    denom=1+np.sum(a*b+b*c+a*c,axis=0)
    return 2*np.arctan2(numer,denom),np.hypot(numer,denom)

def compute(n,valid=None,boundary_tol=1e-8,antipodal_tol=1e-8):
    n=np.asarray(n,float)
    if n.ndim!=3 or n.shape[0]!=3 or min(n.shape[1:])<3:
        raise ValueError("expected 3 x ny x nx Stokes map")
    if valid is None: valid=np.ones(n.shape[1:],bool)
    if not np.all(valid) or not np.isfinite(n).all():
        return {"valid":False,"reason":"null/invalid Stokes samples"}
    lengths=np.linalg.norm(n,axis=0)
    if np.min(lengths)<.5 or np.max(abs(lengths-1))>1e-8:
        return {"valid":False,"reason":"non-unit Stokes vectors"}
    boundary=np.concatenate((n[:,0,:],n[:,-1,:],n[:,:,0],n[:,:,-1]),axis=1)
    err=float(np.max(np.linalg.norm(boundary-boundary[:,0,None],axis=0)))
    if err>boundary_tol:
        return {"valid":False,"reason":"nonconstant boundary; open-patch charge only","boundary_error":err}
    a,b,c,d=n[:,:-1,:-1],n[:,:-1,1:],n[:,1:,1:],n[:,1:,:-1]
    x,den1=solid_angle(a,b,c);y,den2=solid_angle(a,c,d)
    ambiguity=float(min(np.min(den1),np.min(den2)))
    if ambiguity<antipodal_tol:
        return {"valid":False,"reason":"geodesic triangle ambiguous/near-antipodal","minimum_triangle_condition":ambiguity}
    charge=float(np.sum(x+y)/(4*np.pi))
    nearest=int(np.rint(charge))
    return {"valid":True,"geodesic_mesh_charge":charge,"integer_winding_candidate":nearest,
            "distance_to_nearest_integer":abs(charge-nearest),"boundary_error":err,
            "minimum_triangle_condition":ambiguity,
            "rigor":"piecewise-geodesic numerical charge; exact real-number proof not claimed"}

def synthetic_compact_skyrmion(size=161):
    x=np.linspace(-1.2,1.2,size);X,Y=np.meshgrid(x,x)
    r=np.hypot(X,Y);phi=np.arctan2(Y,X)
    angle=np.pi*np.clip(1-r,0,1)
    return np.stack((np.sin(angle)*np.cos(phi),np.sin(angle)*np.sin(phi),np.cos(angle)))

def test():
    cases=[]
    for size in (41,81,161):
        ans=compute(synthetic_compact_skyrmion(size))
        assert ans["valid"] and abs(abs(ans["geodesic_mesh_charge"])-1)<1e-8,ans
        cases.append({"size":size,**ans})
    bad=synthetic_compact_skyrmion(81)
    bad[:,0,0]=[0,1,0]
    assert compute(bad)["valid"] is False
    mask=np.ones((81,81),bool);mask[40,40]=False
    assert compute(synthetic_compact_skyrmion(81),mask)["valid"] is False
    return {"synthetic_closed_boundary_test":"PASS","results":cases,"measured_source_arrays":False,
            "attribution":"Original Dev-Shen 2026 optical supertopologies are external prior work"}

if __name__=="__main__":print(json.dumps(test(),indent=2))
