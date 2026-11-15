#!/usr/bin/env python3
"""Exact integer 27-voxel reaction/transport/circulation regression.

The selected 3x3x3 lattice has 54 unoriented local bonds. Distal vascular
delivery is a *different* directed transport class; a membrane interface
requires an explicit gate. Sources/sinks are separately accounted for.
No kinetic values, permeability coefficients or biological intervention
outcomes are inferred from this synthetic conservation fixture.
"""
from __future__ import annotations

import json
from dataclasses import dataclass
from enum import Enum
from itertools import product

V = tuple(product(range(3), repeat=3))
V_SET = set(V)
LOCAL_BONDS = tuple(
    (p, tuple(p[i] + int(i == axis) for i in range(3)))
    for p in V for axis in range(3) if p[axis] < 2
)
assert len(V) == 27 and len(LOCAL_BONDS) == 54
assert len(set(LOCAL_BONDS)) == 54


class Kind(str, Enum):
    LOCAL = "local"
    VESSEL = "vascular"
    MEMBRANE = "membrane"


@dataclass(frozen=True)
class Edge:
    source: tuple[int, int, int]
    target: tuple[int, int, int]
    kind: Kind
    permitted: bool
    source_reference: str


def validate_edge(edge: Edge):
    if edge.source not in V_SET or edge.target not in V_SET:
        raise ValueError("transport endpoint is outside 3x3x3 lattice")
    if edge.source == edge.target:
        raise ValueError("transport self-loop not admitted")
    if not edge.source_reference.strip():
        raise ValueError("missing explicit origin of physical transport permission")
    if edge.kind == Kind.LOCAL and (
        (edge.source, edge.target) not in LOCAL_BONDS
        and (edge.target, edge.source) not in LOCAL_BONDS
    ):
        raise ValueError("local transfer requires actual 54-bond adjacency")


def push(amounts: dict, edge: Edge, count: int):
    validate_edge(edge)
    if count < 0 or type(count) is not int:
        raise ValueError("exact nonnegative integer transfer required")
    if count and not edge.permitted:
        raise ValueError("transport blocked at non-permeable connection")
    if amounts[edge.source] < count:
        raise ValueError("flux cannot exceed available source inventory")
    updated = amounts.copy()
    updated[edge.source] -= count
    updated[edge.target] += count
    assert sum(updated.values()) == sum(amounts.values())
    return updated


def add_open_sources(amounts: dict, sources: dict, sinks: dict):
    updated = amounts.copy()
    for pos, count in sources.items():
        if pos not in V_SET or type(count) is not int or count < 0:
            raise ValueError("invalid source location or magnitude")
        updated[pos] += count
    for pos, count in sinks.items():
        if pos not in V_SET or type(count) is not int or count < 0:
            raise ValueError("invalid sink location or magnitude")
        if updated[pos] < count:
            raise ValueError("sink draws more material than exists")
        updated[pos] -= count
    assert sum(updated.values()) == sum(amounts.values()) + sum(sources.values()) - sum(sinks.values())
    return updated


def expects_error(fn, *args):
    try:
        fn(*args)
    except ValueError:
        return
    raise AssertionError("invalid transport case accepted")


def main():
    source, neighbor, remote = (0, 0, 0), (1, 0, 0), (2, 2, 2)
    baseline = {v: 0 for v in V}
    baseline[source] = 5
    local = Edge(source, neighbor, Kind.LOCAL, True, "synthetic adjacent conductance")
    blocked_membrane = Edge(neighbor, remote, Kind.MEMBRANE, False, "synthetic gated membrane")
    vascular = Edge(source, remote, Kind.VESSEL, True, "synthetic distal vascular route")

    after_local = push(baseline, local, 2)
    assert after_local[neighbor] == 2 and after_local[remote] == 0
    assert sum(after_local.values()) == 5
    after_distal = push(baseline, vascular, 2)
    assert after_distal[remote] == 2 and sum(after_distal.values()) == 5
    assert after_distal[remote] != after_local[remote]

    expects_error(push, after_local, blocked_membrane, 1)
    expects_error(push, baseline, Edge(source, remote, Kind.LOCAL, True, "fictional local edge"), 1)
    expects_error(push, baseline, Edge(remote, source, Kind.VESSEL, True, ""), 0)
    expects_error(push, baseline, local, 6)
    expects_error(push, baseline, local, -1)

    opened = add_open_sources(after_distal, {source: 3}, {remote: 1})
    assert sum(opened.values()) == 7
    assert opened[remote] == 1

    # Two separately conserved chemical inventories. Redistribution changes
    # local BH4:BH2 without changing whole-tissue inventories.
    bh4 = baseline
    bh2 = {v: 0 for v in V}
    bh2[remote] = 3
    supplied_bh4 = push(bh4, vascular, 2)
    assert sum(supplied_bh4.values()) == sum(bh4.values()) == 5
    assert sum(bh2.values()) == 3
    assert bh4[remote] == 0 and supplied_bh4[remote] == 2
    assert bh2[remote] == 3

    print(json.dumps({
        "status": "passed",
        "nonperiodic_voxels": len(V),
        "nonperiodic_local_bonds": len(LOCAL_BONDS),
        "distal_circulation_edges_require_distinct_source": True,
        "membrane_permissions_enforced": True,
        "synthetic_total_before_and_after_distal_delivery": [5, 5],
        "remote_amount_without_vs_with_vascular_route": [0, 2],
        "open_system_total_after_injection_and_clearance": 7,
        "blocked_edge_and_flux_overdraw_rejected": True,
        "bh4_bh2_totals_vs_local_delivery_distinguished": True,
        "source_phyiscal_rates_calibrated": False,
        "real_vascular_connectome_verified": False,
        "pnf_promotion": False,
    }, indent=2))


if __name__ == "__main__":
    main()
