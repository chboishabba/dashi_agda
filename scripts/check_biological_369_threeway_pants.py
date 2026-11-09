#!/usr/bin/env python3
"""Genuine native 1-to-3 cubical material split with original pants geometry.

The 369 physical junction is (0,0,0), with EXACT native bonds to
(+1,0,0), (0,+1,0), (0,0,+1). One shared 3x3x3 material inventory
is distributed 3 -> 1+1+1; source origin is depleted.
The ORIGINAL 1-to-3 pants has an abstract capacity 3 -> 1+1+1.
This matching selected fixture is not a measured chemical/vascular
flow or a universal identification of pants capacity and molecule count.
"""
from __future__ import annotations

from pathlib import Path
from itertools import product
import json

ROOT=Path(__file__).resolve().parents[1]
OWNER=ROOT/"DASHI/Biology/Physical/Biological369OriginalThreeWayPantsFluxExact.agda"
PTS=tuple(product((-1,0,1),repeat=3))
IDX={p:i for i,p in enumerate(PTS)}
ORIGIN=(0,0,0)
TARGETS=((1,0,0),(0,1,0),(0,0,1))
BONDS=tuple((p,tuple(p[i]+int(i==a) for i in range(3)))
            for p in PTS for a in range(3) if p[a]<1)

def one_transfer(inventory,source,target):
    if (source,target) not in BONDS:
        raise ValueError("source/target are not one canonical positive bond")
    output=inventory.copy()
    if output[IDX[source]]:
        output[IDX[source]]-=1
        output[IDX[target]]+=1
    if sum(output)!=sum(inventory):
        raise AssertionError("shared material conservation failed")
    return output

def split(source_units):
    state=[0]*27
    state[IDX[ORIGIN]]=source_units
    for target in TARGETS:
        state=one_transfer(state,ORIGIN,target)
    return state

def main():
    content=OWNER.read_text()
    for lemma in (
      "originalThreeBranchesSharePhysicalOrigin",
      "originalThreeWayPantsConservesSameInventory",
      "selectedMaterialAmountExactlyThree",
      "selectedBranchedMaterialAmountExactlyThree",
      "xOutputReceivesOne", "yOutputReceivesOne",
      "zOutputReceivesOne", "sourceOriginDepletedAfterThreeTransfers",
      "canonicalOneToThreePantsCapacity",
      "originalPantsInputCapacityEqualsPhysicalFixture",
      "originalPantsOutputCapacityEqualsPhysicalFixture",
      "pantsCapacityDoesNotPayEmpiricalFlux",
    ):
        assert lemma in content,lemma
    assert all((ORIGIN,t) in BONDS for t in TARGETS)
    state=split(3)
    assert state[IDX[ORIGIN]]==0
    assert [state[IDX[t]] for t in TARGETS]==[1,1,1]
    assert sum(state)==3
    cases=0
    for n in range(10):
        result=split(n)
        assert sum(result)==n
        assert result[IDX[ORIGIN]]==max(n-3,0)
        assert sum(result[IDX[t]] for t in TARGETS)==min(n,3)
        cases+=1
    print(json.dumps({
       "status":"passed-native-369-3d-one-to-three-pants-branch",
       "original_physical_cube":[3,3,3],
       "source_junction":list(ORIGIN),
       "native_branch_targets":[list(x) for x in TARGETS],
       "original_native_three_branch_edges":3,
       "selected_initial_material":3,
       "selected_final_branch_amounts":[1,1,1],
       "selected_origin_material_after":0,
       "additional_initial_inventory_cases":cases,
       "global_material_conserved":True,
       "existing_pants_capacity_fixture":[3,1,1,1],
       "generic_pants_capacity_equals_measured_flux":False,
       "measured_permeability_supplied":False,
       "agda_kernel_acceptance":False,
    },indent=2))

if __name__=="__main__":
    main()
