#!/usr/bin/env python3
"""Nonpromotion: the current PL triangulations are NOT Power's (3,6)-tight ones.

Original theorem SOURCE: Stephen C. Power, 'Noncompact surfaces,
triangulations and rigidity', Bull. London Math. Soc. 57 (2025),
2097--2115, DOI 10.1112/blms.70083; the preprint is
arXiv:2403.11986 (2024). Source Theorems 4.5, 6.4: each noncompact
surface ADMITS some countable (3,6)-tight and minimally 3-rigid
triangulation, constructed with special graph operations and
girth/sparsity constraints. This existence theorem is NOT a
certificate for an arbitrary chosen triangulation.

We consume the original DASHI exotic-topology finite PL triangles
rather than inventing separate stages:
  exotic_topology_pl_complement_components.initial/transition
  exotic_topology_balanced_ternary_pl.transition and original marked disk.

For any finite simple graph with >= 3 vertices, (3,6)-sparsity
requires 3|V'|-|E'|>=6 for ALL >=3-vertex subgraphs. If the
whole graph has 3V-E < 6, it already violates sparsity.
3V-E=6 is ONLY a necessary global count, not proof of the
subgraph inequalities. No bar-joint rigidity is inferred.
"""
import json
from exotic_topology_pl_complement_components import (
    initial as initial_standard, transition as transition_standard
)
from exotic_topology_pl_frontier_lineage import mark_initial
from exotic_topology_pl_surface_gluings import disk, sphere_with_holes, edge
from exotic_topology_balanced_ternary_pl import transition as transition_balanced


def graph_signature(mesh):
    faces = mesh.triangles
    vertices = {v for face in faces for v in face}
    edges = {edge(u,v) for a,b,c in faces for u,v in ((a,b),(b,c),(c,a))}
    assert len({frozenset(t) for t in faces}) == len(faces)
    assert len(vertices) >= 3
    maxwell = 3*len(vertices)-len(edges)
    return {
        "vertices": len(vertices),
        "edges": len(edges),
        "triangles": len(faces),
        "maxwell_3V_minus_E": maxwell,
        "violates_full_graph_36_sparsity_if_below_6": maxwell < 6,
        "36_tight_certified": False,
        "minimal_3_rigidity_certified": False,
    }


def audit():
    results = {}
    for family in ("cantor", "loch", "jacob", "balanced_ternary"):
        if family == "balanced_ternary":
            stage, piece = mark_initial(disk(), [()]), sphere_with_holes(3)
            step = lambda x,p:transition_balanced(x,p)
        else:
            stage, piece = initial_standard(family)
            step = lambda x,p:transition_standard(x,p,family)
        states = []
        for n in range(3):
            signature = graph_signature(stage.mesh)
            signature["depth"] = n
            states.append(signature)
            if n != 2:
                stage, receipt = step(stage,piece)
                assert receipt["same_object_old_inclusion"]
        results[family] = states
    assert [s["maxwell_3V_minus_E"] for s in results["cantor"]] == [6,6,6]
    assert [s["maxwell_3V_minus_E"] for s in results["loch"]] == [6,0,-6]
    assert [s["maxwell_3V_minus_E"] for s in results["jacob"]] == [6,-6,-18]
    assert [s["maxwell_3V_minus_E"] for s in results["balanced_ternary"]] == [6,6,6]
    assert all(s["violates_full_graph_36_sparsity_if_below_6"]
               for name in ("loch","jacob")
               for s in results[name][1:])
    return {
        "families": results,
        "source":"Stephen C. Power (2025) DOI 10.1112/blms.70083",
        "source_theorem_is_existence_not_all_triangulations":True,
        "full_graph_maxwell_eq_6_does_not_prove_sparse_subgraphs":True,
        "actual_selected_triangs_36_tight_verified":False,
        "source_kernel_verified":False,
    }


if __name__ == "__main__":
    print(json.dumps(audit(),indent=2,sort_keys=True))
