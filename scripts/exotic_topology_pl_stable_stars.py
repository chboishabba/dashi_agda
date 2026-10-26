#!/usr/bin/env python3
"""Exact finite same-triangulation star-stabilisation for nested PL surfaces.

Owners REUSED:
  exotic_topology_pl_surface_gluings.py: original oriented triangles,
      boundary loops and manifold vertex-link checker;
  exotic_topology_pl_frontier_lineage.py: literal marked boundaries;
  exotic_topology_pl_complement_components.py: original old-simplex
      embedding / outgoing dual component verification;
  exotic_topology_balanced_ternary_pl.py: actual TWO-pants 1->3 junction.

A key necessary property of a valid collared infinite surface is that,
for every vertex v of a compact K_n, its star stabilizes after stage
K_(n+1): every vertex becomes interior, and no additional triangle
ever touches it at later stages. We test the exact finite two-stage
analogue, with actual old-to-new vertex quotient maps, for binary
Cantor, Loch Ness, Jacob's ladder, and 3-way balanced ternary.

This is NOT a construction of the infinite topological colimit. The
all-n uniform collar theorem, compact cofinality, second countability,
and Richards end-space homeomorphism remain independent obligations.

Sources: Brahana (1921) for finite bordered surfaces, Richards (1963)
for the actual infinite ideal boundary. This finite algorithm and
test are DASHI implementation, not source-authored topological proofs.
"""
import json

from exotic_topology_pl_surface_gluings import boundary_loops
from exotic_topology_pl_complement_components import (
    initial as binary_initial, transition as binary_transition,
)
from exotic_topology_balanced_ternary_pl import (
    BRANCHES, transition as ternary_transition,
)
from exotic_topology_pl_frontier_lineage import mark_initial
from exotic_topology_pl_surface_gluings import disk, sphere_with_holes


def vertices(mesh):
    return {v for tri in mesh.triangles for v in tri}


def boundary_vertices(mesh):
    return {v for loop in boundary_loops(mesh)[0] for v in loop}


def simplex_star(mesh, vertex):
    """The exact (unoriented) triangles incident with vertex."""
    return {frozenset(tri) for tri in mesh.triangles if vertex in tri}


def transition(stage, piece, family):
    """Call the EXISTING source-owned stage transition without cloning it."""
    if family == "balanced_ternary":
        return ternary_transition(stage, piece, with_transport=True)
    return binary_transition(stage, piece, family, with_transport=True)


def initial(family):
    if family == "balanced_ternary":
        return mark_initial(disk(), [()]), sphere_with_holes(3)
    return binary_initial(family)


def verify_stable_old_stars(old, mid, later, old_to_mid, mid_to_later):
    """Compare every old vertex star after ONE collar versus after TWO."""
    old_vertices = vertices(old.mesh)
    assert set(old_to_mid) == old_vertices
    assert len(set(old_to_mid.values())) == len(old_vertices)
    assert len(set(mid_to_later.values())) == len(mid_to_later)
    assert all(w in mid_to_later for w in old_to_mid.values())

    mid_boundary = boundary_vertices(mid.mesh)
    later_boundary = boundary_vertices(later.mesh)
    for v in old_vertices:
        w = old_to_mid[v]
        z = mid_to_later[w]
        assert w not in mid_boundary, "old vertex not yet interior"
        assert z not in later_boundary, "old interior vertex re-exposed"
        star_mid = simplex_star(mid.mesh, w)
        transported = {
            frozenset(mid_to_later[k] for k in tri)
            for tri in star_mid
        }
        actual = simplex_star(later.mesh, z)
        assert len(star_mid) == len(transported), "triangle folded"
        assert transported == actual, (
            "future attachment changed an old vertex star",
            v, w, z, len(transported), len(actual),
        )
    return {
        "old_vertices_verified": len(old_vertices),
        "all_old_vertices_interior_after_one_stage": True,
        "all_old_vertex_stars_stable_after_two_stages": True,
        "old_triangle_count": len(old.mesh.triangles),
        "mid_triangle_count": len(mid.mesh.triangles),
        "later_triangle_count": len(later.mesh.triangles),
    }


def audit(two_step_windows=2):
    assert 1 <= two_step_windows <= 3
    receipts = {}
    for family in ("cantor", "loch", "jacob", "balanced_ternary"):
        old, piece = initial(family)
        windows = []
        for n in range(two_step_windows):
            mid, mreceipt, old_to_mid = transition(old, piece, family)
            later, lreceipt, mid_to_later = transition(mid, piece, family)
            result = verify_stable_old_stars(
                old, mid, later, old_to_mid, mid_to_later,
            )
            assert mreceipt["same_object_old_inclusion"]
            assert lreceipt["same_object_old_inclusion"]
            assert mreceipt["geometric_child_incidence_verified"]
            assert lreceipt["geometric_child_incidence_verified"]
            windows.append({"depth": n, **result})
            # Sliding window, not an invented bridge across separate
            # surfaces. Next window uses the ACTUAL mid stage.
            old = mid
        receipts[family] = windows
    return {
        "families": receipts,
        "status": "PASS finite simplicial old-vertex-star stabilization",
        "same_object_triangle_transport": True,
        "infinite_pl_colimit_proved": False,
        "richards_end_space_homeomorphism_proved": False,
        "kernel_verified": False,
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
