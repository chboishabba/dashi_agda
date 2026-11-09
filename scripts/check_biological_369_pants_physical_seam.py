#!/usr/bin/env python3
"""Original 3x3x3 geometry with explicit physical pants-seam receipt.

This regression checks the exact original selected 369 line:
  (-1,0,0) -> (0,0,0) -> (+1,0,0)
and preserves one shared 27-site inventory under the two consecutive
native nearest-neighbour transfers. It also checks 54 distinct original
bonds and 36 native plaquettes, separating a PHYSICAL material
conservation proof from a FORMAL pants/cobordism InterfaceMatch.

The original DASHI pants channels have five attributes:
proposition/capacity/phase/wave/openness. Their typed equality is a
source-written Agda proof, not evidence of membrane conductance.
"""
from __future__ import annotations

from itertools import product
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]
OWNERS = (
    ROOT / "DASHI/Biology/Physical/Biological369PantsPhysicalSeamExact.agda",
    ROOT / "DASHI/Biology/Physical/Biological369CubicalMaterialFieldExact.agda",
)
PTS = tuple(product((-1,0,1), repeat=3))
IDX = {p:i for i,p in enumerate(PTS)}
BONDS = tuple(
    (p, tuple(p[i] + int(i==a) for i in range(3)))
    for p in PTS for a in range(3) if p[a] < 1
)
assert len(PTS)==27 and len(BONDS)==54
assert len({b for b in BONDS})==54

def move(state, a, b):
    assert (a,b) in BONDS or (b,a) in BONDS
    target=state.copy()
    if target[IDX[a]]:
        target[IDX[a]]-=1
        target[IDX[b]]+=1
    assert sum(target)==sum(state)
    return target

def main():
    source1=OWNERS[0].read_text()
    source2=OWNERS[1].read_text()
    for symbol in (
        "canonical369PhysicalPantsSeam",
        "gluedSeamTransportPreservesOriginalTotal",
        "seamPropositionAgrees", "seamCapacityAgrees",
        "seamPhaseAgrees", "seamWaveAgrees",
        "seamOpennessAgrees", "noAutomaticPhysicalFlowFromPants",
    ):
        assert symbol in source1, symbol
    for symbol in (
        "CubicalMaterialField", "originalCubeReadoutRoundTrip",
        "originalVectorReadoutRoundTrip", "originalCubicalPlaquetteCount",
    ):
        assert symbol in source2, symbol

    a,b,c=(-1,0,0),(0,0,0),(1,0,0)
    assert (a,b) in BONDS and (b,c) in BONDS
    count=0
    for start in range(27):
        for q in range(4):
            state=[0]*27
            state[start]=q
            intermediate=move(state,a,b)
            final=move(intermediate,b,c)
            assert sum(final)==q
            count+=1
    supplied=[0]*27
    supplied[IDX[a]]=1
    observed=move(move(supplied,a,b),b,c)
    assert observed[IDX[c]]==1
    # Distinguish separately connected and physically gated seam.
    blocked=move(supplied,a,b)
    assert blocked[IDX[c]]==0
    assert sum(blocked)==sum(observed)==1

    # Count actual elementary squares on three axes:
    squares=tuple(
        (p, ax, ay) for p in PTS for ax in range(3)
        for ay in range(ax+1,3)
        if p[ax]<1 and p[ay]<1
    )
    assert len(squares)==36
    assert IDX[a]!=IDX[b]!=IDX[c]
    print(json.dumps({
        "status":"passed-original-cubical-pants-seam-synthetic-transport",
        "semantic_carrier":"SSPTrit^3 original Ternary27Point",
        "storage":"lossless 27-entry vector chart",
        "original_voxels":len(PTS),
        "native_positive_bonds":len(BONDS),
        "native_plaquettes":len(squares),
        "physically_incident_seam_bonds":[[a,b],[b,c]],
        "shared_inventory_traces_checked":count,
        "same_total_gated_vs_passable_distinct_target":True,
        "pants_five_coordinate_interface_is_not_physiological_permeability":True,
        "source_paid_flow_rate":False,
        "agda_kernel_accepted":False,
    }, indent=2))

if __name__=="__main__":
    main()
