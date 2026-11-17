#!/usr/bin/env python3
"""Same-graph spherical capping certificate for source-owned finite Cantor PL stages.

Original mathematical roots:
  Euler planar graph inequalities and the compact orientable
  surface classification attributed to Brahana (1921);
  Power (2025), DOI 10.1112/blms.70083, for the modern
  (3,6)-tight noncompact triangulation existence theorem.
  Power's selected rigid graph construction is NOT claimed
  identical to the present finite triangles.

Original finite PL owners REUSED:
  exotic_topology_pl_surface_gluings.Mesh, inspect, boundary_loops;
  exotic_topology_pl_complement_components.initial/transition;
  exotic_topology_balanced_ternary_pl.transition.

For all tested POSITIVE depths of the TWO genus-zero families:
- every boundary circle is already a three-edge polygon;
- add the oppositely oriented missing triangle on each;
- no ORIGINAL vertex or edge changes;
- the resulting actual finite simplicial complex is a closed
  connected orientable genus-zero triangulated surface (sphere).
Thus the original 1-skeleton has an explicitly supplied
planar embedding. Combined with 3V-E=6 and the CLASSICAL
planar graph bound E'<=3V'-6 on all >=3-vertex subgraphs,
the original selected graph is mathematically (3,6)-tight.
This is not a Python proof of that theorem, nor a kernel
certificate of planar embeddings, nor a minimally 3-rigid
3D realisation.

The depth-0 SINGLE TRIANGLE K3 is handled directly:
adding an equal reverse face would be a duplicate 2-simplex
(not an abstract simplicial sphere) and must NOT be accepted
as a same-graph simplicial spherical cap.
"""
import json
from exotic_topology_pl_surface_gluings import (
    Mesh, disk, sphere_with_holes, inspect, boundary_loops, edge
)
from exotic_topology_pl_frontier_lineage import mark_initial
from exotic_topology_pl_complement_components import (
    initial as standard_initial, transition as standard_transition,
)
from exotic_topology_balanced_ternary_pl import transition as balanced_transition


def graph_sets(mesh):
    vertices = {v for t in mesh.triangles for v in t}
    edges = {edge(a,b) for t in mesh.triangles for a,b in
             ((t[0],t[1]),(t[1],t[2]),(t[2],t[0]))}
    return vertices, edges


def cap_boundary_triangles(mesh):
    loops = boundary_loops(mesh)[0]
    assert all(len(cycle) == 3 for cycle in loops)
    original_faces = {frozenset(t) for t in mesh.triangles}
    cap_faces = [(a,c,b) for a,b,c in loops]
    assert all(frozenset(t) not in original_faces for t in cap_faces), (
        "not an abstract simplicial sphere: duplicate 2-simplex"
    )
    assert len({frozenset(t) for t in cap_faces}) == len(cap_faces)
    capped = Mesh(mesh.triangles + cap_faces, mesh.label + "+closedSphereCaps")
    assert graph_sets(capped) == graph_sets(mesh), (
        "a spherical cap changed the original graph's vertices or edges"
    )
    assert inspect(capped, (0,0))["boundaries"] == 0
    return capped


def audit(depth=2):
    assert 1 <= depth <= 3
    result = {}
    for family in ("cantor", "balanced_ternary"):
        if family == "cantor":
            stage, piece = standard_initial(family)
            next_stage = lambda m,p: standard_transition(m,p,"cantor")
        else:
            stage, piece = mark_initial(disk(),[()]), sphere_with_holes(3)
            next_stage = balanced_transition
        stages = []
        for n in range(depth + 1):
            original = inspect(stage.mesh)
            assert original["genus"] == 0
            V,E=map(len,graph_sets(stage.mesh))
            assert 3*V-E==6
            if n == 0:
                assert len(stage.mesh.triangles) == 1
                assert V == E == 3
                try:
                    cap_boundary_triangles(stage.mesh)
                except AssertionError:
                    pass
                else:
                    raise AssertionError("invalid duplicate triangle sphere cap accepted")
                status = "K3 planar by direct three-vertex embedding"
            else:
                capped=cap_boundary_triangles(stage.mesh)
                assert inspect(capped,(0,0))["genus"] == 0
                status = "same-graph explicit simplicial 2-sphere cap"
            stages.append({
                "depth":n,
                "boundary_count":original["boundaries"],
                "vertices":V,
                "edges":E,
                "maxwell":3*V-E,
                "planarity_witness":status,
                "all_subgraph_sparsity_kernel_proved":False,
            })
            if n<depth:
                stage,certificate=next_stage(stage,piece)
                assert certificate["same_object_old_inclusion"]
        result[family]=stages
    return {
        "families":result,
        "same_graph_spherical_caps_verified":True,
        "classical_planar_edge_bound_required_for_36_tight":True,
        "power_minimal_3_rigidity_proved":False,
        "lean_agda_kernel_verified":False,
    }


if __name__=="__main__":
    print(json.dumps(audit(),indent=2,sort_keys=True))
