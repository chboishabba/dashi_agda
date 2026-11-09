#!/usr/bin/env python3
"""Exact per-voxel signed charge continuity on original ternary 3x3x3.

Selected physically typed cation/anion carrier (z=+1 or -1).
Each directed original bond transport debits its actual source and
credits its actual target on ONE shared inventory. The independent
incidence divergence is signed +J at departure and -J at arrival.
For every voxel p, and any sequential collection of events:

   Q_after(p) - Q_before(p) + div(J)(p) = q_external(p)

Only original six-face sites may receive environmental q_external.
When the source is empty, actual J=0. No measured ionic mobility,
bulk Poisson electric field or biochemical membrane channel inferred.
"""
from __future__ import annotations
import json
from itertools import product
from pathlib import Path

PTS=tuple(product((-1,0,1),repeat=3))
IDX={p:i for i,p in enumerate(PTS)}
BONDS=tuple((p,tuple(p[i]+int(i==a) for i in range(3)))
  for p in PTS for a in range(3) if p[a]<1)
FACES={(a,s):frozenset(p for p in PTS if p[a]==s)
  for a in range(3) for s in (-1,1)}
assert len(PTS)==27 and len(BONDS)==54
ROOT=Path(__file__).resolve().parents[1]
OWNER=ROOT/"DASHI/Biology/Physical/Biological369CubicalOpenSignedChargeExact.agda"


def start():
    return {+1:[0]*27,-1:[0]*27}


def local_charge(state):
    return tuple(state[+1][i]-state[-1][i] for i in range(27))


def apply(state,action,divergence,external):
    before=local_charge(state)
    new={key:val.copy() for key,val in state.items()}
    new_div=divergence.copy()
    new_external=external.copy()
    if action[0]=="bond":
        _,sign,a,b=action
        if sign not in (+1,-1) or ((a,b) not in BONDS and (b,a) not in BONDS):
            raise ValueError("not a native original signed ion bond")
        if new[sign][IDX[a]]>0:
            new[sign][IDX[a]]-=1
            new[sign][IDX[b]]+=1
            j=sign
            new_div[IDX[a]]+=j
            new_div[IDX[b]]-=j
    elif action[0]=="face":
        _,sign,face,p,n,kind=action
        if sign not in (+1,-1) or face not in FACES or p not in FACES[face]:
            raise ValueError("environmental source not on true outer face")
        if type(n) is not int or n<0 or kind not in ("inject","extract"):
            raise ValueError("invalid environmental current/event")
        if kind=="inject":
            new[sign][IDX[p]]+=n
            new_external[IDX[p]]+=sign*n
        else:
            actual=min(n,new[sign][IDX[p]])
            new[sign][IDX[p]]-=actual
            new_external[IDX[p]]-=sign*actual
    else:
        raise ValueError("untyped physical event")
    # Strict support check independently of the charge-divergence formula:
    # a real bond may alter ONLY its actual geometric endpoints, and a
    # certified environmental event may alter ONLY its OnFace voxel.
    # In particular this rejects compensating fictional remote changes
    # that could leave a global conservation check falsely satisfied.
    allowed={IDX[action[2]],IDX[action[3]]} if action[0]=="bond" else {IDX[action[3]]}
    for charge_sign in (+1,-1):
        changed={i for i in range(27)
                 if new[charge_sign][i]!=state[charge_sign][i]}
        assert changed.issubset(allowed),(action,charge_sign,changed)
    after=local_charge(new)
    # The global divergence/exchange arrays are cumulative since
    # the start of this transport history. Per-event check separately
    # subtracts old cumulative divergence/external source amounts.
    for i in range(27):
        assert (
            after[i]-before[i]+(new_div[i]-divergence[i])
            ==new_external[i]-external[i]
        ), (action,i)
    return new,new_div,new_external


def check_trace(state,actions):
    origin=local_charge(state)
    div=[0]*27
    ext=[0]*27
    for action in actions:
        state,div,ext=apply(state,action,div,ext)
    current=local_charge(state)
    for i in range(27):
        assert current[i]-origin[i]+div[i]==ext[i]
    assert sum(div)==0
    return state,div,ext


def main():
    content=OWNER.read_text()
    for name in (
        "nativeSignedChargeWithEnvironmentalSourcesAndSinks",
        "originalFullSpatialOpenSignedChargeBalance",
    ):
        assert name in content,name

    checks=0
    for z in (+1,-1):
        for start_p in PTS:
            for reverse in (False,True):
                state=start()
                state[z][IDX[start_p]]=2
                actions=[
                    ("bond",z,b if reverse else a,a if reverse else b)
                    for a,b in BONDS
                ]
                check_trace(state,actions)
                checks+=len(actions)

    first=(-1,0,0)
    second=(0,0,0)
    third=(0,0,1)
    original=start()
    original[+1][IDX[first]]=4
    original[-1][IDX[third]]=1
    actions=[
        ("bond",+1,first,second),
        ("bond",+1,second,(1,0,0)),
        ("face",+1,(0,-1),first,2,"inject"),
        ("face",-1,(2,+1),third,2,"inject"),
        ("bond",-1,third,second),
        ("face",+1,(0,-1),first,3,"extract"),
        ("face",-1,(2,+1),third,3,"extract"),
    ]
    _,div,ext=check_trace(original,actions)
    assert sum(div)==0
    assert any(ext)

    invalid=[
        ("bond",+1,first,(1,1,1)),
        ("face",+1,(0,-1),second,1,"inject"),
        ("face",-1,(2,+1),third,-1,"inject"),
    ]
    for action in invalid:
        try:
            check_trace(start(),[action])
        except ValueError:
            pass
        else:
            raise AssertionError("nonphysical divergence/face event admitted")

    print(json.dumps({
      "status":"passed-synthetic-local-3d-signed-charge-continuity",
      "original_cube":[3,3,3],
      "native_bonds":len(BONDS),
      "outer_faces":len(FACES),
      "directed_ion_event_checks":checks,
      "per_voxel_continuity_witnesses_per_event":27,
      "mixed_transport_and_environmental_history_passed":True,
      "global_divergence_cancels":True,
      "local_continuity": "Q_after-Q_before+divJ=q_external",
      "actual_PNP_fields_solved":False,
      "source_rates_calibrated":False,
      "agda_kernel_accepted":False,
    },indent=2))


if __name__=="__main__":
    main()
