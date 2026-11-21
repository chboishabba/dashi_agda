#!/usr/bin/env python3
"""Exact finite compartment, circulation and redox counterexamples.

A circulating BH4 measure is not an intracellular BH4 pool. BH4/BH2
amounts at different regions and transport gates must be represented
separately. Synthetic witnesses only; not permeability/clinical evidence.
"""
from __future__ import annotations

import json
from collections import deque
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OWNER = ROOT / "DASHI/Biology/BH4SpatialConnectivityCirculationExact.agda"


def reachable(source, target, permitted):
    fringe = deque([source])
    visited = {source}
    while fringe:
        node = fringe.popleft()
        if node == target:
            return True
        for a, b in permitted:
            if a == node and b not in visited:
                visited.add(b)
                fringe.append(b)
    return False


def move_once(amounts, source, target, allowed):
    if not allowed:
        return amounts.copy()
    if amounts[source] < 1:
        return amounts.copy()
    nxt = amounts.copy()
    nxt[source] -= 1
    nxt[target] += 1
    assert sum(nxt.values()) == sum(amounts.values())
    return nxt


def main():
    content = OWNER.read_text(encoding="utf-8")
    owners = (
        "transportIfConnectedConservesTotal",
        "transportIfConnectedConservesCharge",
        "globalInventoryCannotDetermineLocalDelivery",
        "forwardDeliveryPath",
        "reversePathNotProvided",
        "sameTotalBH4", "sameTotalBH2",
        "totalsAloneCannotDetermineLocalCofactor",
        "bloodBrainBarrierTransfer", "vascularPerfusion",
        "plasmaMembraneTransfer", "gapJunctionTransfer",
        "classifyPermittedFlow",
    )
    for owner in owners:
        assert owner in content, f"missing original Agda physical proof owner {owner}"

    sites = ("blood", "endothelium", "brain")
    vascular = {("blood", "endothelium")}
    bbb_permitted = False
    assert reachable("blood", "endothelium", vascular)
    assert not reachable("endothelium", "blood", vascular)
    assert not reachable("blood", "brain", vascular)

    initial = {"blood": 1, "endothelium": 0, "brain": 0}
    delivered = move_once(initial, "blood", "endothelium", True)
    denied = move_once(initial, "blood", "endothelium", False)
    assert sum(delivered.values()) == sum(denied.values()) == 1
    assert delivered["endothelium"] == 1 and denied["endothelium"] == 0

    # Same global BH4/BH2 totals, opposite target-local reduced/cofactor
    # availability in a two-compartment synthetic redox arrangement.
    a = {"BH4": (1, 0), "BH2": (0, 1)}
    b = {"BH4": (0, 1), "BH2": (1, 0)}
    assert sum(a["BH4"]) == sum(b["BH4"]) == 1
    assert sum(a["BH2"]) == sum(b["BH2"]) == 1
    assert a["BH4"][1] == 0 and b["BH4"][1] == 1

    # No assumption that crossing a BBB or cell membrane is a permanently
    # binary Boolean: this fixture tests source and permeability requirements.
    assert bbb_permitted is False
    print(json.dumps({
        "status": "passed",
        "selected_toy_regions": list(sites),
        "global_pool_equal_but_target_delivery_different": True,
        "same_global_BH4_and_BH2_distinct_target_BH4": True,
        "directed_reachability_non_symmetric": True,
        "missing_bbb_transport_permission_not_assumed": True,
        "source_original_kinetic_constants": False,
        "patient_or_clinical_claim": False,
    }, indent=2))


if __name__ == "__main__":
    main()
