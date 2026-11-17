#!/usr/bin/env python3
"""Same-event Gielis/Kozyrev optical SI bridge, USING original PR #1404.

The original source owner is:
  chboishabba/dashi_agda PR #1404
  scripts/kozyrev_optical_event_ledger.py
This script dynamically loads that exact original RayLedger from a
provided checkout/worktree. IT DOES NOT REIMPLEMENT RayLedger.

For one supplied physical event stream, independently accumulate
the EXACT Fraction signed radiation-pressure torque, wall force,
absorption and output power. Execute the identical events through
the original Kozyrev RayLedger and compare its observable output.

Nothing here claims that a synthetic fixture was measured.
The original source owner can be supplied via --owner-path or
KOZYREV_RAY_LEDGER_PATH. Missing owner FAILS CLOSED.

Do not use a random Python module with a matching class name;
the direct source SHA256 is reported so the execution is replayable.
"""
from __future__ import annotations
from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import math
import os

from gielis_kozyrev_pr1404_bridge import ORIGINAL_GIT_BLOBS,PR1404
ORIGINAL_BLOB=ORIGINAL_GIT_BLOBS["kozyrev_optical_event_ledger.py"]
C=F(299792458)

def frac(v):
    if isinstance(v,F):return v
    if isinstance(v,float):raise ValueError("physical source inputs must be exact decimal strings or rationals, not floats")
    return F(str(v))

def vec(v):
    if len(v)!=2:raise ValueError("2D vector required")
    return tuple(frac(x) for x in v)

def cross(a,b):
    return a[0]*b[1]-a[1]*b[0]

def sub(a,b):
    return (a[0]-b[0],a[1]-b[1])

def summ(a,b):
    return (a[0]+b[0],a[1]+b[1])

def scl(k,v):
    return (k*v[0],k*v[1])

def exact_ray_ledger(source,events,terminal,axis_origin):
    P=frac(source["power_W"])
    if P<0:raise ValueError("power must be nonnegative")
    direction=vec(source["direction"])
    origin=vec(source["point"])
    axis=vec(axis_origin)
    if direction[0]**2+direction[1]**2!=1:
        raise ValueError("source must be unit vector exactly")
    wall_force=(F(0),F(0));wall_torque=F(0);absorbed=F(0)
    power=P;position=origin
    for e in events:
        point=vec(e["point"]);out=vec(e["outgoing_direction"])
        eta=frac(e["reflectivity"])
        if not 0<=eta<=1:raise ValueError("invalid reflectivity")
        if out[0]**2+out[1]**2!=1:raise ValueError("outgoing must be unit exactly")
        distance=sub(point,position)
        if cross(distance,direction)!=0 or distance[0]*direction[0]+distance[1]*direction[1]<=0:
            raise ValueError("hit must be on current forward ray")
        momentum_in=scl(power/C,direction)
        momentum_out=scl(power*eta/C,out)
        impulse=sub(momentum_in,momentum_out)
        wall_force=summ(wall_force,impulse)
        wall_torque+=cross(sub(point,axis),impulse)
        absorbed+=power*(1-eta)
        power*=eta
        position=point;direction=out
    final_position=vec(terminal["point"]);kind=terminal["kind"]
    if kind not in ("target","escape","unresolved"):raise ValueError("invalid terminal kind")
    final_segment=sub(final_position,position)
    if cross(final_segment,direction)!=0 or final_segment[0]*direction[0]+final_segment[1]*direction[1]<0:
        raise ValueError("terminal off forward ray")
    source_momentum=scl(P/C,vec(source["direction"]))
    final_momentum=scl(power/C,direction)
    momentum_residual=sub(source_momentum,summ(wall_force,final_momentum))
    input_angular=cross(sub(origin,axis),source_momentum)
    output_angular=cross(sub(final_position,axis),final_momentum)
    angular_residual=input_angular-wall_torque-output_angular
    energy_residual=P-absorbed-power
    return {
      "wall_torque_Nm":wall_torque,
      "wall_force_N":wall_force,
      "wall_absorption_W":absorbed,
      "output_W":power,
      "momentum_residual_N":momentum_residual,
      "angular_residual_Nm":angular_residual,
      "energy_residual_W":energy_residual,
      "event_count":len(events),
      "kind":kind,
    }

def load_original_ray_ledger(path):
    path=Path(path).resolve()
    if not path.is_file():raise FileNotFoundError(f"original Kozyrev PR #1404 RayLedger source missing: {path}")
    contents=path.read_bytes()
    actual_git_blob=hashlib.sha1(
        b"blob "+str(len(contents)).encode()+b"\x00"+contents).hexdigest()
    if actual_git_blob!=ORIGINAL_BLOB:
        raise ValueError(
            "original Kozyrev RayLedger blob mismatch: "
            +actual_git_blob+" != "+ORIGINAL_BLOB
        )
    if b"class RayLedger:" not in contents or b"def hit(" not in contents or b"def close(" not in contents:
        raise ValueError("not the expected original Kozyrev RayLedger owner")
    spec=importlib.util.spec_from_file_location("kozyrev_original_pr1404_rayledger",path)
    module=importlib.util.module_from_spec(spec)
    import sys
    sys.modules[spec.name]=module
    spec.loader.exec_module(module)
    return module,hashlib.sha256(contents).hexdigest()

def compare_with_original(owner_path,scene):
    module,digest=load_original_ray_ledger(owner_path)
    source=scene["source"];hits=scene["hits"];terminal=scene["terminal"]
    axis=scene.get("axis_origin",["0","0"])
    exact=exact_ray_ledger(source,hits,terminal,axis)
    ledger=module.RayLedger.emit(
        tuple(map(float,vec(source["point"]))),
        tuple(map(float,vec(source["direction"]))),
        float(frac(source["power_W"])),
        axis_origin=tuple(map(float,vec(axis)))
    )
    for hit in hits:
        ledger.hit(
            tuple(map(float,vec(hit["point"]))),
            tuple(map(float,vec(hit["outgoing_direction"]))),
            float(frac(hit["reflectivity"]))
        )
    original=ledger.close(terminal["kind"],tuple(map(float,vec(terminal["point"]))))
    for key in ("wall_torque_Nm","wall_absorption_W","output_W","energy_residual_W","angular_residual_Nm"):
        expected=float(exact[key]);actual=float(original[key])
        if not math.isclose(expected,actual,rel_tol=1e-11,abs_tol=2e-11):
            raise AssertionError(f"{key}: exact {expected} vs original {actual}")
    for i,(expected,actual) in enumerate(zip(exact["wall_force_N"],original["wall_force_N"])):
        if not math.isclose(float(expected),float(actual),rel_tol=1e-11,abs_tol=2e-11):
            raise AssertionError(f"wall_force_N[{i}] mismatch")
    assert original["kind"]==exact["kind"]
    assert original["event_count"]==exact["event_count"]
    assert exact["energy_residual_W"]==0
    assert exact["angular_residual_Nm"]==0
    return {
      "status":"SAME_EVENT_ORIGINAL_KOZYREV_GIELIS_OPTICAL_PARITY",
      "original_owner":"PR #1404 scripts/kozyrev_optical_event_ledger.py",
      "original_owner_pr_head":PR1404,
      "original_owner_git_blob_verified":True,
      "original_owner_git_blob":ORIGINAL_BLOB,
      "original_owner_sha256":digest,
      "geometry":"original event stream, not separately generated Gielis collision list",
      "input_source":scene,
      "exact_signed_torque_Nm":str(exact["wall_torque_Nm"]),
      "original_rayledger_signed_torque_Nm":original["wall_torque_Nm"],
      "exact_wall_force_N":[str(t) for t in exact["wall_force_N"]],
      "exact_absorbed_power_W":str(exact["wall_absorption_W"]),
      "exact_output_power_W":str(exact["output_W"]),
      "energy_residual_exact_zero":True,
      "angular_residual_exact_zero":True,
      "original_event_parity":True,
      "scene_is_measurement":False,
      "same_Gielis_collision_solver_event_stream_verified":False,
      "same_physical_apparatus_calibrated":False,
    }

def synthetic_two_hit_fixture():
    # Exact right-angle two-hit optical source. Both impacts lie on
    # the previous outgoing ray, including a NONZERO angular impulse
    # about a deliberately noncentral selected axis.
    return {
      "source":{"point":["-2","0"],"direction":["1","0"],"power_W":"9000"},
      "axis_origin":["-1","1"],
      "hits":[
        {"point":["0","0"],"outgoing_direction":["0","1"],"reflectivity":"19/20"},
        {"point":["0","2"],"outgoing_direction":["-1","0"],"reflectivity":"4/5"},
      ],
      "terminal":{"kind":"escape","point":["-2","2"]},
    }

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--owner-path",default=os.environ.get("KOZYREV_RAY_LEDGER_PATH"))
    parser.add_argument("--scene-json",help="optional EXACT decimal-string/rational event stream")
    args=parser.parse_args()
    if not args.owner_path:parser.error("--owner-path is required (original PR #1404 checkout)")
    scene=json.loads(Path(args.scene_json).read_text()) if args.scene_json else synthetic_two_hit_fixture()
    print(json.dumps(compare_with_original(args.owner_path,scene),sort_keys=True,indent=2))
if __name__=="__main__":
    main()
