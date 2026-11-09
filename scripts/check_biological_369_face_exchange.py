#!/usr/bin/env python3
"""Exact nonnegative open finite-volume boundary exchange on original 3x3x3.

Only six actual outer cube faces are admitted. Each contains nine voxels.
Input and *actual* extracted material are accounted for separately.
Every chronological face event acts on the same 27-site inventory;
zero-source outflow is stationary, not a negative molecule count.
No physiological face permeability, flow rate or measured boundary
conditions are supplied by this synthetic invariant regression.
"""
from __future__ import annotations

from itertools import product
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parents[1]
OWNER=ROOT/"DASHI/Biology/Physical/Biological369CubicalBoundaryMaterialExact.agda"
PTS=tuple(product((-1,0,1),repeat=3))
IDX={p:i for i,p in enumerate(PTS)}
FACES={(axis,sign):tuple(p for p in PTS if p[axis]==sign)
       for axis in range(3) for sign in (-1,1)}
assert len(FACES)==6 and all(len(nodes)==9 for nodes in FACES.values())


def boundary_event(state,face,point,number,kind):
    if face not in FACES or point not in FACES[face]:
        raise ValueError("injection/clearance site lacks physical outer-face proof")
    if type(number) is not int or number<0:
        raise ValueError("no invented negative source/sink")
    if kind not in ("inject","extract"):
        raise ValueError("typed environmental direction required")
    nxt=state.copy()
    if kind=="inject":
        nxt[IDX[point]]+=number
        actual_in,actual_out=number,0
    else:
        actual_out=min(number,nxt[IDX[point]])
        nxt[IDX[point]]-=actual_out
        actual_in=0
    assert min(nxt)>=0
    assert sum(nxt)+actual_out==sum(state)+actual_in
    return nxt,actual_in,actual_out


def main():
    text=OWNER.read_text()
    for name in (
        "everyOriginalOuterFaceHasNineVoxels",
        "eachOriginalBoundaryInjectionIsPaid",
        "outflowMaterialBalance",
        "originalFaceExchangeBalance",
        "allOriginalBoundaryExchangeHistoriesBalance",
        "originalOuterFacePoints",
    ):
        assert name in text,name

    checked=0
    for site in PTS:
        for face,nodes in FACES.items():
            if site not in nodes:
                try:
                    boundary_event([0]*27,face,site,1,"inject")
                except ValueError:
                    continue
                raise AssertionError("accepted interior/non-face source")
            for n in range(4):
                for initial in range(4):
                    state=[0]*27
                    state[IDX[site]]=initial
                    for kind in ("inject","extract"):
                        nxt,inp,out=boundary_event(state,face,site,n,kind)
                        assert sum(nxt)+out==initial+inp
                        checked+=1
    # Same shared state; two crossed outer faces; extract cap
    # must use actual amount, not a requested unpayable withdrawal.
    actions=[
        ((0,-1),(-1,0,0),3,"inject"),
        ((1,1),(-1,1,0),2,"inject"),
        ((0,-1),(-1,0,0),5,"extract"),
        ((1,1),(-1,1,0),1,"extract"),
    ]
    state=[0]*27
    incoming=outgoing=0
    for face,site,n,kind in actions:
        state,inp,out=boundary_event(state,face,site,n,kind)
        incoming+=inp;outgoing+=out
    assert incoming==5 and outgoing==4
    assert sum(state)==1
    assert sum(state)+outgoing==incoming

    print(json.dumps({
        "status":"passed-original-cubical-open-face-exchange",
        "original_cube_shape":[3,3,3],
        "native_six_faces":6,
        "face_voxels_each":9,
        "total_boundary_voxel_face_incidence":54,
        "source_sink_single_step_checks":checked,
        "open_history_input":incoming,
        "open_history_actual_output":outgoing,
        "open_history_final_material":sum(state),
        "open_history_exact_balance":True,
        "original_boundary_conditions_calibrated":False,
        "agda_kernel_receipt":False,
    },indent=2))

if __name__=="__main__":
    main()
