#!/usr/bin/env python3
"""Exact finite PL complement-component bridge for three surface exhaustions.

Consume ORIGINAL geometry and actual marked-frontier ownership:
  exotic_topology_pl_surface_gluings.py
  exotic_topology_pl_frontier_lineage.py

For each K_n -> K_(n+1), compute the literal new triangles, the
dual-graph connected components of K_(n+1)\K_n in the finite
triangulation, their interface edges with the embedded K_n,
and their outgoing boundary circles. Verify a BIJECTION between
old outgoing boundary components and newly attached exterior
components, with exact Cantor binary child counts (2) or
Loch/Jacob persistent counts (1).

This pays the finite, source-specific same-object complementary
incidence condition ignored by pure Euler/genus/prefix counts.

NOT PAID: open connected components of an infinite topological
complement; collar homeomorphism/topological direct limit; compact
cofinality; Richards end space, end genus or classification.

Source roots: H. R. Brahana (1921) compact bordered surfaces;
B. Kerekjarto (1923) earlier ideal-boundary classification;
Ian Richards (1963) noncompact surface ideal boundaries.
Algorithm is repository-local, not attributable to those authors.
"""
from collections import defaultdict, deque
import json

from exotic_topology_pl_surface_gluings import (
    disk, sphere_with_holes, torus_with_holes, edge,
    boundary_loops,
)
from exotic_topology_pl_frontier_lineage import mark_initial, attach


def triangle_edges(t):
    a, b, c = t
    return (edge(a, b), edge(b, c), edge(c, a))


def dual_components(triangles, subset):
    """Connected components under full shared-edge adjacency."""
    edges = defaultdict(list)
    for idx in subset:
        for e in triangle_edges(triangles[idx]):
            edges[e].append(idx)
    adj = defaultdict(set)
    for owners in edges.values():
        assert len(owners) <= 2
        if len(owners) == 2:
            p, q = owners
            adj[p].add(q)
            adj[q].add(p)
    remaining = set(subset)
    result = []
    while remaining:
        first = min(remaining)
        remaining.remove(first)
        queue = deque((first,))
        component = {first}
        while queue:
            for neighbor in adj[queue.popleft()]:
                if neighbor in remaining:
                    remaining.remove(neighbor)
                    component.add(neighbor)
                    queue.append(neighbor)
        result.append(component)
    return result


def verify_complement_components(old, new, embedding, family):
    """Finite combinatorial comparison on the EXACT embedded old surface."""
    # The old triangulation is embedded simplexwise in the new one:
    image = {frozenset(embedding[v] for v in tri) for tri in old.mesh.triangles}
    all_faces = [frozenset(tri) for tri in new.mesh.triangles]
    assert len(image) == len(old.mesh.triangles)
    assert all(len(face) == 3 for face in image)
    assert len(set(all_faces)) == len(all_faces)
    assert image <= set(all_faces), "old simplices not contained in new stage"

    old_boundary = {
        key: {edge(embedding[u], embedding[v])
              for u, v in zip(loop, loop[1:] + loop[:1])}
        for key, loop in old.frontier.items()
    }
    assert all(len(es) == len(old.frontier[key]) for key, es in old_boundary.items())
    boundary_owner = {e: key for key, es in old_boundary.items() for e in es}
    assert len(boundary_owner) == sum(len(x) for x in old_boundary.values())

    added_ids = {i for i, face in enumerate(all_faces) if face not in image}
    components = dual_components(new.mesh.triangles, added_ids)
    assert len(components) == len(old.frontier), (
        "wrong number of geometric outgoing complementary components",
        family, len(components), len(old.frontier),
    )

    # An internal old boundary edge is now incident with one old and one
    # new face. Classify each added component by these exact interface
    # edges, NOT by an address supplied separately from the geometry.
    outside = {}
    for idx in added_ids:
        for e in triangle_edges(new.mesh.triangles[idx]):
            if e in boundary_owner:
                outside.setdefault(e, set()).add(idx)
    assert set(outside) == set(boundary_owner)
    assert all(len(v) == 1 for v in outside.values())

    output_boundaries = {
        key: {edge(u, v) for u, v in zip(loop, loop[1:] + loop[:1])}
        for key, loop in new.frontier.items()
    }
    # Every new outgoing edge is incident with exactly one added face.
    new_edge_owners = defaultdict(set)
    for idx in added_ids:
        for e in triangle_edges(new.mesh.triangles[idx]):
            new_edge_owners[e].add(idx)
    assert all(e in new_edge_owners for es in output_boundaries.values() for e in es)

    seen_parents = set()
    parent_to_children = {}
    for component in components:
        touching = {
            boundary_owner[e]
            for e, ids in outside.items() if ids <= component
        }
        assert len(touching) == 1, (
            "different old boundary components accidentally connected",
            family, touching,
        )
        parent = next(iter(touching))
        assert parent not in seen_parents
        seen_parents.add(parent)
        # Every interface edge of this parent must belong to the same
        # piece component, not only one chosen vertex or sample edge.
        assert all(outside[e] <= component for e in old_boundary[parent])

        child_keys = {
            key for key, es in output_boundaries.items()
            if any(new_edge_owners[e] <= component for e in es)
        }
        for key in child_keys:
            assert all(new_edge_owners[e] <= component
                       for e in output_boundaries[key])
        expected = (
            {parent + (0,), parent + (1,)} if family == "cantor"
            else {parent + (-1,), parent + (0,), parent + (1,)}
                 if family == "balanced_ternary"
            else {parent}
        )
        assert child_keys == expected, (
            "outgoing geometric boundaries differ from original old branch",
            family, parent, child_keys, expected,
        )
        parent_to_children[str(parent)] = {
            "children": sorted(map(str, child_keys)),
            "component_triangles": len(component),
            "old_boundary_edges": len(old_boundary[parent]),
        }
    assert seen_parents == set(old.frontier)
    assert len(set().union(*components)) == len(added_ids)
    return {"family": family, "components": len(components),
            "old_boundaries": len(old.frontier),
            "new_boundaries": len(new.frontier),
            "added_triangles": len(added_ids),
            "same_object_old_inclusion": True,
            "each_old_boundary_has_one_complement_component": True,
            "geometric_child_incidence_verified": True,
            "parent_to_children": parent_to_children}


def initial(family):
    if family == "cantor":
        return mark_initial(disk(), [()]), sphere_with_holes(3)
    if family == "loch":
        return mark_initial(disk(), [()]), torus_with_holes(2)
    if family == "jacob":
        return mark_initial(sphere_with_holes(2), [("L",), ("R",)]), torus_with_holes(2)
    raise ValueError(family)


def transition(stage, piece, family):
    old = stage
    old_keys = tuple(sorted(old.frontier))
    # Track inclusion of EVERY old vertex through all successive
    # applications of the single authoritative glue implementation.
    vertex_map = {v: v for tri in old.mesh.triangles for v in tri}
    for key in old_keys:
        children = (key + (0,), key + (1,)) if family == "cantor" else (key,)
        stage, carrier = attach(stage, piece, key, children, with_transport=True)
        vertex_map = {v: carrier[image] for v, image in vertex_map.items()}
    receipt = verify_complement_components(old, stage, vertex_map, family)
    return stage, receipt


def audit(max_depth=3):
    results = {}
    for family in ("cantor", "loch", "jacob"):
        stage, piece = initial(family)
        checks = []
        for depth in range(max_depth):
            stage, receipt = transition(stage, piece, family)
            stage.verify(
                (0, 2**(depth+1)) if family == "cantor" else
                (depth+1, 1) if family == "loch" else
                (2*(depth+1), 2)
            )
            checks.append({"depth": depth, **receipt})
        results[family] = checks
    return {
        "families": results,
        "max_transition_depth": max_depth,
        "finite_pl_inclusion_and_complement_components": True,
        "richards_infinite_end_space_proved": False,
        "kernel_verified": False,
    }


if __name__ == "__main__":
    print(json.dumps(audit(), sort_keys=True, indent=2))
