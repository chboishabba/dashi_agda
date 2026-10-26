#!/usr/bin/env python3
"""Exact frontier-lineage audits for the finite PL exotic-surface constructions.

Motivation: merely observing b_n = 2^n does NOT prove the Cantor end
space. An implementation that repeatedly attaches to boundary index
zero may split a newly created child twice while leaving an old
frontier branch unsplit. This layer labels every outgoing geometric
boundary circle, transports its vertices across the existing exact
oriented gluing, and checks the entire old-to-new ancestry relation.

Uses the ORIGINAL construction and vertex-link validator in
exotic_topology_pl_surface_gluings.py; no triangulation duplication.

Source attribution: compact bordered surfaces Brahana (1921),
ideal-boundary surface classification/realisation Kerékjártó (1923)
and Richards (1963). An infinite collared direct-limit manifold and
topological identification of ALL ends remain independent obligations.
"""
from dataclasses import dataclass
import json

from exotic_topology_pl_surface_gluings import (
    Mesh, boundary_loops, disk, glue, inspect, sphere_with_holes,
    torus_with_holes,
)


@dataclass
class MarkedSurface:
    mesh: Mesh
    # Each key is an EXACT lineage key: tuple of binary digits for the
    # Cantor frontiers, or ('L',)/('R',)/() for the 1/2-ended stages.
    frontier: dict

    def verify(self, expected=None):
        result = inspect(self.mesh, expected)
        loops = boundary_loops(self.mesh)[0]
        actual = {frozenset(loop) for loop in loops}
        supplied = [frozenset(vertices) for vertices in self.frontier.values()]
        assert len(set(supplied)) == len(supplied), "two labels refer to one frontier"
        assert set(supplied) == actual, "missing/spurious geometric frontier label"
        assert len(self.frontier) == result["boundaries"]
        return result


def mark_initial(mesh, labels):
    loops = sorted(boundary_loops(mesh)[0], key=lambda loop: min(loop))
    assert len(labels) == len(loops)
    stage = MarkedSurface(mesh, dict(zip(labels, loops)))
    stage.verify()
    return stage


def attach(stage, piece, target, children, with_transport=False):
    """Attach to ONE named old boundary; optionally retain vertex inclusion.

    The optional map is the exact old-stage simplicial injection into
    the newly triangulated stage; original callers remain unchanged.
    """
    assert target in stage.frontier
    assert len(children) == len(set(children))
    assert all(child not in (set(stage.frontier) - {target}) for child in children)
    old_loops = boundary_loops(stage.mesh)[0]
    match = [i for i, loop in enumerate(old_loops)
             if frozenset(loop) == frozenset(stage.frontier[target])]
    assert len(match) == 1
    old_idx = match[0]
    new_loops = boundary_loops(piece)[0]
    incoming = 0
    outgoing = sorted((loop for j, loop in enumerate(new_loops)
                       if j != incoming), key=lambda loop: min(loop))
    assert len(outgoing) == len(children)
    new_mesh, old_map, added_map = glue(
        stage.mesh, piece, old_idx, incoming, with_transport=True
    )
    other = {key: tuple(old_map[v] for v in loop)
             for key, loop in stage.frontier.items() if key != target}
    fresh = {key: tuple(added_map[v] for v in loop)
             for key, loop in zip(children, outgoing)}
    assert not set(other).intersection(fresh)
    result = MarkedSurface(new_mesh, {**other, **fresh})
    result.verify()
    return (result, old_map) if with_transport else result


def staged(family, max_depth=4):
    if family == "cantor":
        stage = mark_initial(disk(), [()])
        piece = sphere_with_holes(3)
    elif family == "loch":
        stage = mark_initial(disk(), [()])
        piece = torus_with_holes(2)
    elif family == "jacob":
        stage = mark_initial(sphere_with_holes(2), [("L",), ("R",)])
        piece = torus_with_holes(2)
    else:
        raise ValueError(family)

    outcomes = []
    for n in range(max_depth + 1):
        old_keys = tuple(sorted(stage.frontier))
        if family == "cantor":
            assert set(old_keys) == {
                tuple(int(ch) for ch in format(k, f"0{n}b")) if n else ()
                for k in range(2 ** n)
            }
            want = (0, 2 ** n)
        elif family == "loch":
            assert old_keys == ((),)
            want = (n, 1)
        else:
            assert old_keys == (("L",), ("R",))
            want = (2 * n, 2)
        geometric = stage.verify(want)
        outcomes.append({"depth": n, "frontier_keys": tuple(old_keys),
                         "genus": geometric["genus"],
                         "boundary_count": geometric["boundaries"],
                         "vertex_links_verified": geometric["vertex_links_verified"]})
        if n == max_depth:
            break
        # Snapshot only OLD labels, so newborn children cannot be
        # inadvertently selected again in the same stage.
        for old in old_keys:
            descendants = (old + (0,), old + (1,)) if family == "cantor" else (old,)
            stage = attach(stage, piece, old, descendants)
        next_keys = set(stage.frontier)
        expected = ({old + (bit,) for old in old_keys for bit in (0, 1)}
                    if family == "cantor" else set(old_keys))
        assert next_keys == expected, "an old boundary was not split exactly once"
        assert all(
            sum(child[:len(parent)] == parent for child in next_keys) ==
            (2 if family == "cantor" else 1)
            for parent in old_keys
        )
    return outcomes


def audit(max_depth=4):
    families = {name: staged(name, max_depth)
                for name in ("cantor", "loch", "jacob")}
    assert families["cantor"][-1]["boundary_count"] == 2 ** max_depth
    assert families["loch"][-1]["genus"] == max_depth
    assert families["jacob"][-1]["genus"] == 2 * max_depth
    return {
        "families": families,
        "status": "PASS oriented PL stage and exact frontier lineage; infinite end homeomorphism OPEN",
        "limitation": "finite-stage labels alone do not establish topological end-space compactness, Hausdorffness or an actual direct-limit manifold",
    }


if __name__ == "__main__":
    print(json.dumps(audit(), sort_keys=True, indent=2))
