#!/usr/bin/env python3
"""Exact integer signed charge across native 54-bond and outer-face events.

Independent finite semantics for the Agda
Biological369CubicalOpenSignedChargeExact owner. Real 3x3x3 sites,
six outer faces, actual directed source/target, no fictional interior
boundary supply. Explicit observed withdrawal (not requested overdraw).
Cation/anion pair carries original integer signed net electric charge.

THIS IS A SYNTHETIC DISCRETE INVARIANT, NOT A PNP/vascular calibration.
"""
from __future__ import annotations
import json
from itertools import product
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
OWNER=ROOT/"DASHI/Biology/Physical/Biological369CubicalOpenSignedChargeExact.agda"
PTS=tuple(product((-1,0,1),repeat=3))
IDX={p:i for i,p in enumerate(PTS)}
BONDS=tuple((p,tuple(p[i]+int(i==a) for i in range(3)))
  for p in PTS for a in range(3) if p[a]<1)
FACES={(a,s):frozenset(p for p in PTS if p[a]==s)
       for a in range(3) for s in (-1,1)}
assert len(PTS)==27 and len(BONDS)==54
assert len(FACES)==6 and all(len(v)==9 for v in FACES.values())


def initial():
    return {z:[0]*27 for z in (-1,+1)}


def signed(inventory):
    return sum(inventory[+1])-sum(inventory[-1])


def transfer(inventory,sign,a,b):
    if sign not in inventory or ((a,b) not in BONDS and (b,a) not in BONDS):
        raise ValueError("invalid signed native-bond transfer")
    dst={q:v.copy() for q,v in inventory.items()}
    if dst[sign][IDX[a]]:
        dst[sign][IDX[a]]-=1
        dst[sign][IDX[b]]+=1
    assert signed(dst)==signed(inventory)
    return dst


def face_event(inventory,sign,face,point,requested,incoming):
    if sign not in inventory or face not in FACES or point not in FACES[face]:
        raise ValueError("nonphysical face or ionic sign")
    if type(requested) is not int or requested<0 or type(incoming) is not bool:
        raise ValueError("invalid signed source magnitude")
    dst={q:v.copy() for q,v in inventory.items()}
    old=signed(inventory)
    if incoming:
        dst[sign][IDX[point]]+=requested
        paid_in,paid_out=requested,0
    else:
        paid_out=min(requested,dst[sign][IDX[point]])
        dst[sign][IDX[point]]-=paid_out
        paid_in=0
    assert signed(dst)+sign*paid_out==old+sign*paid_in
    assert all(n>=0 for x in dst.values() for n in x)
    return dst,paid_in,paid_out


def main():
    contents=OWNER.read_text()
    for lemma in (
        "positiveOpenMaterialBalance",
        "negativeOpenMaterialBalance",
        "nativeSignedChargeWithEnvironmentalSourcesAndSinks",
        "originalFullSpatialOpenSignedChargeBalance",
        "selectedNativeOpenIonicFixtureBalances",
    ):
        assert lemma in contents,lemma

    tested=0
    for q in (-1,+1):
        for start in PTS:
            for reverse in (False,True):
                ions=initial()
                ions[q][IDX[start]]=4
                prior=signed(ions)
                for a,b in BONDS:
                    ions=transfer(ions,q,b if reverse else a,
                                      a if reverse else b)
                    tested+=1
                assert signed(ions)==prior

    # Full mixed open history:
    # same starting state, internally distributed across true 3D bonds,
    # then externally charged/uncharged by selected actual exterior faces.
    system=initial()
    system[+1][IDX[(-1,0,0)]]=3
    system[-1][IDX[(1,0,0)]]=2
    before=signed(system)
    for a,b in BONDS:
        system=transfer(system,+1,a,b)
        system=transfer(system,-1,b,a)
    source_charge=sink_charge=0
    events=(
      (+1,(0,-1),(-1,-1,0),3,True),
      (-1,(0,+1),(1,+1,0),2,True),
      (+1,(0,-1),(-1,0,0),7,False),
      (-1,(0,+1),(1,0,0),7,False),
    )
    for sign,face,point,n,incoming in events:
        system,inp,out=face_event(system,sign,face,point,n,incoming)
        source_charge+=sign*inp
        sink_charge+=sign*out
    assert signed(system)+sink_charge==before+source_charge
    assert min(system[+1])>=0 and min(system[-1])>=0

    print(json.dumps({
      "status":"passed-3d-signed-open-ionic-conservation-synthetic",
      "physical_cube":[3,3,3],
      "actual_local_bonds":len(BONDS),
      "actual_outer_faces":len(FACES),
      "face_voxels_each":9,
      "native_internal_signed_transfers_tested":tested,
      "combined_boundary_input_signed":source_charge,
      "combined_boundary_output_signed":sink_charge,
      "final_signed_inventory":signed(system),
      "initial_signed_inventory":before,
      "final_plus_output_equals_initial_plus_input":True,
      "physical_poisson_gauss_law_solved":False,
      "original_electrodiffusive_rate_measured":False,
      "agda_kernel_acceptance":False,
    },indent=2))

if __name__=="__main__":
    main()
