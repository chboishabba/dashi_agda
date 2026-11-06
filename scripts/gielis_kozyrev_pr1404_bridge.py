#!/usr/bin/env python3
"""Gielis baseline -> ORIGINAL DASHI PR #1404 Kozyrev owners, no duplicate physics.

The old PR is OPEN and on a different Git ref. Supply a local checkout of
its scripts with --legacy-dir, or check out PR #1404 before comparing.
An absent source is an explicit NOT_CHECKED receipt, never a pass.
Canonical first-forward owner:
  kozyrev_first_forward_intersection_referee.py @ PR1404 337aabb00
Canonical momentum/power owner:
  kozyrev_optical_event_ledger.py @ PR1404 337aabb00

The geometry m arbitrary, epsilon=0 is the same CENTERLINE as the
Kozyrev 'log' family, matched by inner/outer/turns/growth/srot.
This identity does not identify original HTML stroked-SDF thickness
with independent normal-offset walls.
"""
from __future__ import annotations
import argparse, hashlib, importlib.util, json, math, pathlib
import numpy as np
import gielis_base369_experiments as G

PR1404 = "337aabb00ed54bc1a4c28ada48364cb4dc54d46e"
ORIGINAL_FILES = (
    "kozyrev_first_forward_intersection_referee.py",
    "kozyrev_optical_event_ledger.py",
)
ORIGINAL_GIT_BLOBS = {
    "kozyrev_first_forward_intersection_referee.py":
        "30c6f3021f32769d153aa9afb17cc6a38d55b90d",
    "kozyrev_optical_event_ledger.py":
        "6f89d38c6509ccbc332d066829cbddf620844b64",
}

def git_blob_sha(path):
    content=path.read_bytes()
    return hashlib.sha1(b"blob "+str(len(content)).encode()
                        +b"\x00"+content).hexdigest()

START = np.array([1.05,0.],dtype=float)

def legacy_geometry(inner=.75,outer=1.55,turns=1.5,thickness=0.):
    if not (0<inner<outer and turns>0 and thickness>=0):
        raise ValueError("invalid matched geometry")
    return {"inner":inner,
            "growth":math.log(outer/inner)/(2*math.pi*turns),
            "turns":turns,"thick":thickness,
            "srot":0.,"family":"log"}

def gielis_offset_surfaces(segments, thickness):
    """Independent Gielis log-baseline normal offsets and endcaps.

    Matches Kozyrev PR1404 log-family centreline and normal-offset
    geometry in literal parameter space. Does NOT model HTML stroked SDF.
    """
    if segments < 100 or thickness < 0:
        raise ValueError("bad geometry discretisation")
    theta=np.linspace(0,3*math.pi,segments+1)
    b=math.log(1.55/.75)/(3*math.pi)
    r=.75*np.exp(b*theta)
    x=r*np.cos(theta);y=r*np.sin(theta)
    tx=b*r*np.cos(theta)-r*np.sin(theta)
    ty=b*r*np.sin(theta)+r*np.cos(theta)
    norm=np.hypot(tx,ty)
    nx=-ty/norm; ny=tx/norm
    half=thickness/2
    sides=(np.column_stack((x+half*nx,y+half*ny)),
           np.column_stack((x-half*nx,y-half*ny)))
    caps=(np.array([sides[0][0],sides[1][0]]),
          np.array([sides[0][-1],sides[1][-1]]))
    return sides+caps


def locate_modules(legacy_dir=None):
    folder=(pathlib.Path(legacy_dir) if legacy_dir else pathlib.Path(__file__).parent)
    missing=[name for name in ORIGINAL_FILES if not (folder/name).is_file()]
    if missing:
        return None,{"status":"NOT_CHECKED","missing_original_files":missing,
                     "original_pr":1404,"source_commit":PR1404,
                     "original_HTML_SDF_parity":False}
    mismatches=[
        {"path":name,"expected":ORIGINAL_GIT_BLOBS[name],
         "actual":git_blob_sha(folder/name)}
        for name in ORIGINAL_FILES
        if git_blob_sha(folder/name)!=ORIGINAL_GIT_BLOBS[name]
    ]
    if mismatches:
        return None,{"status":"WRONG_SOURCE","original_pr":1404,
                     "source_commit":PR1404,
                     "source_blob_mismatches":mismatches,
                     "original_HTML_SDF_parity":False}
    loaded=[]
    for name in ORIGINAL_FILES:
        spec=importlib.util.spec_from_file_location(
            "original_"+name.replace(".py",""),folder/name)
        module=importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        loaded.append(module)
    return tuple(loaded),None

def match_original_owners(legacy_dir=None,segments=1536,power_w=100.,
                          first_hit_rays=48,thickness=0.):
    if segments<100 or first_hit_rays<1 or power_w<=0:
        raise ValueError("bad matched benchmark")
    modules,not_checked=locate_modules(legacy_dir)
    if modules is None:return not_checked
    First,Ledger=modules
    g=legacy_geometry(thickness=thickness)
    outer=G.spiral_vertices(3,0.,segments)
    sides=First.surfaces(g,samples=segments)
    # Only for zero wall thickness are the original offset walls
    # identical to the Gielis centreline; not an HTML SDF equivalence.
    # Compare TWO INDEPENDENT constructors for the exact same
    # finite-thickness normal-offset curve (including end caps).
    generated=gielis_offset_surfaces(segments,thickness)
    original_polylines=[
        np.concatenate((a,b[-1:]),axis=0) for a,b in sides
    ]
    wall_error=max(float(np.max(np.linalg.norm(a-b,axis=1)))
                   for a,b in zip(generated,original_polylines))
    if wall_error>1e-12:
        raise AssertionError("Kozyrev reference normal-offset geometry mismatch")
    centreline_error=wall_error if thickness==0 else None
    eps=.003 # original PR1404 first_cross admission threshold
    differences=[];pairs=0;skipped=0
    for j in range(first_hit_rays):
        theta=2*math.pi*(j+.319)/first_hit_rays
        direction=np.array([math.cos(theta),math.sin(theta)])
        independent=First.first_cross(sides,START,direction,epsilon=eps)
        possible=[G.nearest_hit(START,direction,poly)
                  for poly in generated]
        finite=[hit[0] for hit in possible if hit is not None]
        other=min((t for t in finite if t>eps),default=math.inf)
        if not math.isfinite(independent) and not math.isfinite(other):
            continue
        if not math.isfinite(independent) or not math.isfinite(other):
            skipped+=1
            continue
        pairs+=1
        differences.append(abs(float(independent)-float(other)))
    # Cross-check the ORIGINAL power/reflectivity/momentum ledger at
    # one single specular hit of the shared 0-thickness baseline.
    ledger_residuals=[]
    if thickness==0:
        for j in range(first_hit_rays):
            theta=2*math.pi*(j+.319)/first_hit_rays
            direction=np.array([math.cos(theta),math.sin(theta)])
            hit=G.nearest_hit(START,direction,outer)
            if hit is None or hit[0]<=eps:continue
            _,point,normal,_=hit
            outgoing=Ledger.specular(tuple(direction),tuple(normal))
            ledger=Ledger.RayLedger.emit(
                tuple(START),tuple(direction),power_w)
            ledger.hit(tuple(point),outgoing,1.)
            closed=ledger.close("unresolved",
                tuple(point+np.array(outgoing)*0.1))
            target_torque=power_w/Ledger.C*float(G.cross(
                point,direction-np.array(outgoing)))
            if abs(closed["wall_torque_Nm"]-target_torque)>1e-13:
                raise AssertionError("cross-owner SI torque mismatch")
            if abs(closed["angular_residual_Nm"])>1e-12:
                raise AssertionError("Kozyrev angular residual failed")
            if abs(closed["momentum_residual_N"])>1e-12:
                raise AssertionError("Kozyrev momentum residual failed")
            ledger_residuals.append(closed)
            if len(ledger_residuals)>=8:break
    return {
        "status":"CENTRELINE_PARITY_CHECKED" if thickness==0
                 else "OFFSET_WALL_REFEREE_PARITY_CHECKED",
        "original_pr":1404,"source_commit":PR1404,
        "geometry":g,"segments":segments,"rays":first_hit_rays,
        "matched_centreline_max_position_error_m":centreline_error,
        "matched_normal_offset_wall_max_position_error_m":wall_error,
        "wall_thickness_m":thickness,
        "legacy_wall_representation":"normal_offset_with_flat_endcaps",
        "paired_first_hits":pairs,
        "first_hit_comparison_skipped":skipped,
        "first_hit_max_difference_m":max(differences,default=None),
        "power_ledger_event_count":len(ledger_residuals),
        "max_angular_residual_Nm":max(
            (abs(x["angular_residual_Nm"]) for x in ledger_residuals),default=None),
        "max_momentum_residual_N":max(
            (abs(x["momentum_residual_N"]) for x in ledger_residuals),default=None),
        "original_HTML_SDF_parity":False,
        "legacy_finite_thickness_HTML_scene_identified":False,
    }

if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--legacy-dir")
    p.add_argument("--require-legacy",action="store_true")
    p.add_argument("--segments",type=int,default=1536)
    p.add_argument("--rays",type=int,default=48)
    p.add_argument("--power-watts",type=float,default=100.)
    p.add_argument("--thickness",type=float,default=0.)
    p.add_argument("--output")
    args=p.parse_args()
    result=match_original_owners(
        args.legacy_dir,args.segments,args.power_watts,
        args.rays,args.thickness)
    if args.require_legacy and result["status"] in ("NOT_CHECKED","WRONG_SOURCE"):
        raise SystemExit("Original PR1404 owners missing: "+str(result))
    data=json.dumps(result,indent=2,sort_keys=True)
    if args.output:pathlib.Path(args.output).write_text(data+"\n")
    print(data)
