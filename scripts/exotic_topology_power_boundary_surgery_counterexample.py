#!/usr/bin/env python3
"""Counterexample to 'fix genus by boundary subdivision alone'.

SOURCE ROOT: Stephen C. Power (2025), Noncompact surfaces,
triangulations and rigidity, DOI:10.1112/blms.70083, Theorems 4.5
and 6.4 and the constructive moves of section 4.

Consumes the ORIGINAL finite oriented surface builders in:
  exotic_topology_pl_surface_gluings.py,
  exotic_topology_pl_complement_components.py.

Power's (3,6)-tightness requires BOTH the global Maxwell count
3|V|-|E|=6 AND 3|S|-|E(S)|>=6 for every subgraph with >=3
vertices. The Euler-Maxwell lemma gives the NECESSARY boundary
budget L=3b+6g for each genus-g bordered surface.

A tempting shortcut is to add exactly 6g boundary vertices via
edge subdivision. This script constructs the actual refined PL
triangulation (retaining orientability and genus) and checks that
its WHOLE graph has Maxwell count 6. Yet the old vertex set
induces a dense subgraph with f<6. Thus the selected construction
is NOT (3,6)-sparse, despite passing the global budget.

This is a precise negative test of ONE shortcut, not a theorem
that no special Power-style triangulation exists. The original
mesh, its 2D topology, source papers and authorship are unchanged.
"""
import json
from exotic_topology_pl_surface_gluings import (
    Mesh, edge, boundary_loops, inspect
)
from exotic_topology_pl_complement_components import (
    initial, transition
)


def edges(mesh):
    return {edge(u,v) for tri in mesh.triangles
            for u,v in ((tri[0],tri[1]),(tri[1],tri[2]),(tri[2],tri[0]))}


def vertex_set(mesh):
    return {v for tri in mesh.triangles for v in tri}


def split_one_boundary_edge(mesh):
    """PL subdivision of one edge on the FIRST actual boundary loop.

    The unique incident oriented triangle (u,v,t) is replaced by
    (u,w,t),(w,v,t), where w is fresh. This preserves genus and
    orientation, adds 1V, 2E, 1F and increases L by one.
    """
    loops, owners = boundary_loops(mesh)
    assert loops and len(loops[0]) >= 3
    u,v = loops[0][0], loops[0][1]
    candidates = [i for i, tri in enumerate(mesh.triangles)
                  if u in tri and v in tri]
    assert len(candidates)==1
    idx=candidates[0]
    tri=mesh.triangles[idx]
    matching=[tri[(i+2)%3] for i in range(3)
              if tri[i]==u and tri[(i+1)%3]==v]
    assert len(matching)==1, "boundary edge not oriented correctly"
    third=matching[0]
    w=max(vertex_set(mesh))+1
    faces=list(mesh.triangles)
    faces[idx]=(u,w,third)
    faces.append((w,v,third))
    subdivided=Mesh(faces, mesh.label+"+boundary-edge-split")
    before, after=inspect(mesh),inspect(subdivided)
    assert before["genus"]==after["genus"]
    assert before["boundaries"]==after["boundaries"]
    assert after["vertices"]==before["vertices"]+1
    assert after["edges"]==before["edges"]+2
    assert after["triangles"]==before["triangles"]+1
    return subdivided


def attempted_global_repair(family):
    assert family in ("loch","jacob")
    stage, piece=initial(family)
    stage, _=transition(stage,piece,family)
    source=stage.mesh
    geom=inspect(source)
    genus,b=geom["genus"],geom["boundaries"]
    assert genus>0
    old_vertices=vertex_set(source)
    source_boundary_length=sum(len(l) for l in boundary_loops(source)[0])
    assert source_boundary_length==3*b

    repaired=source
    for _ in range(6*genus):
        repaired=split_one_boundary_edge(repaired)

    revised=inspect(repaired)
    length=sum(len(l) for l in boundary_loops(repaired)[0])
    all_edges=edges(repaired)
    full=3*revised["vertices"]-len(all_edges)
    # Do not confuse a necessary global equality with full sparsity.
    assert length==3*b+6*genus
    assert (revised["genus"],revised["boundaries"])==(genus,b)
    assert full==6
    # The *literal old source vertices* survive untouched, except
    # an original boundary edge has been subdivided. They witness
    # failure of the universal sparse-subgraph condition.
    core_edges={e for e in all_edges if e[0] in old_vertices
                and e[1] in old_vertices}
    core_maxwell=3*len(old_vertices)-len(core_edges)
    assert len(old_vertices)>=3 and core_maxwell<6
    return {
        "family":family, "genus":genus, "boundary_count":b,
        "original_boundary_length":source_boundary_length,
        "necessary_boundary_length":3*b+6*genus,
        "subdivision_count":6*genus,
        "revised_whole_graph_maxwell":full,
        "old_vertex_core_size":len(old_vertices),
        "old_vertex_core_edges_after_refinement":len(core_edges),
        "old_vertex_induced_subgraph_maxwell":core_maxwell,
        "global_budget_met":True,
        "true_36_sparsity_rejected_by_explicit_old_core":True,
        "rigidity_proved":False
    }


def audit():
    loch=attempted_global_repair("loch")
    jacob=attempted_global_repair("jacob")
    assert (loch["old_vertex_core_size"],
            loch["old_vertex_core_edges_after_refinement"],
            loch["old_vertex_induced_subgraph_maxwell"]) == (36,107,1)
    assert (jacob["old_vertex_core_size"],
            jacob["old_vertex_core_edges_after_refinement"],
            jacob["old_vertex_induced_subgraph_maxwell"]) == (218,659,-5)
    return {
       "status":"PASS exact PL numerical-repair counterexample",
       "cases":[loch,jacob],
       "all_selected_genus_topologies_preserved":True,
       "necessary_budget_does_not_ensure_subgraph_sparsity":True,
       "next_original_source_donor":"Power (2025) boundary girth, 0-extension, vertex splitting and rigid subgraph substitution",
       "original_existence_theorem_not_contradicted":True,
       "agda_or_lean_kernel_verified":False
    }


if __name__=="__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
