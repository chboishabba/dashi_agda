#!/usr/bin/env python3
"""Explicit oriented PL finite surface exhaustions, not just Euler profiles.

Source: Ian Richards (1963), DOI 10.2307/1993768; elementary oriented
triangulations and boundary-circle gluings. Build literal finite meshes,
verify every vertex link is an interval/circle, global orientation,
connectedness, Euler/genus and actual boundary cycles.

No infinite collared union, decorated end-space homeomorphism or
Richards-classification theorem is asserted by a finite Python test.
"""
from collections import defaultdict, deque
from dataclasses import dataclass
import json


@dataclass
class Mesh:
    triangles: list
    label: str = ""


def sphere_with_holes(holes):
    """Outward-oriented cube-boundary triangulation; remove separated faces."""
    N = 5
    verts, xyz, faces, centers = {}, [], [], []

    def V(coords):
        key = tuple(coords)
        if key not in verts:
            verts[key] = len(verts)
            xyz.append(key)
        return verts[key]

    for axis, sign in ((0, -1), (0, 1), (1, -1), (1, 1), (2, -1), (2, 1)):
        def point(i, j):
            p = [None] * 3
            p[axis] = sign * N
            rest = [a for a in range(3) if a != axis]
            p[rest[0]], p[rest[1]] = -N + 2 * i, -N + 2 * j
            return tuple(p)

        for i in range(N):
            for j in range(N):
                a, b = V(point(i, j)), V(point(i + 1, j))
                c, d = V(point(i + 1, j + 1)), V(point(i, j + 1))
                for tri in ((a, b, c), (a, c, d)):
                    p, q, r = [xyz[v] for v in tri]
                    e = [q[k] - p[k] for k in range(3)]
                    f = [r[k] - p[k] for k in range(3)]
                    normal = e[(axis + 1) % 3] * f[(axis + 2) % 3] - e[(axis + 2) % 3] * f[(axis + 1) % 3]
                    faces.append(tri if normal * sign > 0 else (tri[0], tri[2], tri[1]))
                if i == 2 and j == 2:
                    centers.append(len(faces) - 1)
    assert holes <= len(centers)
    removed = set(centers[:holes])
    return Mesh([t for i, t in enumerate(faces) if i not in removed], f"sphere-{holes}")


def torus_with_holes(holes):
    """Periodic 6x6 triangular torus, two distant triangular holes."""
    N = 6

    def v(i, j):
        return (i % N) * N + j % N

    faces, centers = [], []
    for i in range(N):
        for j in range(N):
            a, b, c, d = v(i, j), v(i + 1, j), v(i + 1, j + 1), v(i, j + 1)
            faces.extend(((a, b, c), (a, c, d)))
            if (i, j) in ((0, 0), (3, 3)):
                centers.append(len(faces) - 1)
    assert holes <= len(centers)
    removed = set(centers[:holes])
    return Mesh([t for i, t in enumerate(faces) if i not in removed], f"torus-{holes}")


def disk():
    return Mesh([(0, 1, 2)], "disk")


def edge(u, v):
    return (min(u, v), max(u, v))


def boundary_loops(mesh):
    edges = defaultdict(list)
    for a, b, c in mesh.triangles:
        for u, v in ((a, b), (b, c), (c, a)):
            edges[edge(u, v)].append((u, v))
    for pieces in edges.values():
        assert len(pieces) in (1, 2)
        if len(pieces) == 2:
            assert pieces[0] == pieces[1][::-1]
    outgoing = defaultdict(list)
    for pieces in edges.values():
        if len(pieces) == 1:
            u, v = pieces[0]
            outgoing[u].append(v)
    assert all(len(v) == 1 for v in outgoing.values())
    visited, loops = set(), []
    for start in outgoing:
        if start in visited:
            continue
        loop, v = [], start
        while v not in visited:
            visited.add(v)
            loop.append(v)
            v = outgoing[v][0]
        assert v == start
        loops.append(tuple(loop))
    assert len(visited) == len([e for e in edges.values() if len(e) == 1])
    return loops, edges


class DSU:
    def __init__(self, n):
        self.parent = list(range(n))

    def find(self, x):
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def union(self, a, b):
        a, b = self.find(a), self.find(b)
        if a != b:
            self.parent[b] = a


def glue(a, b, which_a=0, which_b=0, with_transport=False):
    """Identify matched oriented polygonal circles.

    Optional exact vertex transport prevents losing frontier identity
    when an earlier boundary is removed and fresh child circles arise.
    Existing callers still receive only the Mesh.
    """
    av = boundary_loops(a)[0][which_a]
    bv = boundary_loops(b)[0][which_b]
    assert len(av) == len(bv)
    offset = max(x for tri in a.triangles for x in tri) + 1
    whole = a.triangles + [tuple(x + offset for x in tri) for tri in b.triangles]
    uf = DSU(max(x for tri in whole for x in tri) + 1)
    for i, v in enumerate(av):
        uf.union(v, offset + bv[-i % len(bv)])
    roots = sorted({uf.find(x) for tri in whole for x in tri})
    rename = {v: i for i, v in enumerate(roots)}
    result = Mesh([tuple(rename[uf.find(x)] for x in tri) for tri in whole], a.label + "+" + b.label)
    if not with_transport:
        return result
    left_vertices = {v for tri in a.triangles for v in tri}
    right_vertices = {v for tri in b.triangles for v in tri}
    left_map = {v: rename[uf.find(v)] for v in left_vertices}
    right_map = {v: rename[uf.find(v + offset)] for v in right_vertices}
    # Each input triangulated subspace embeds in the glued finite
    # surface; vertex identifications occur ACROSS the two pieces,
    # never between two distinct vertices of the same input.
    assert len(set(left_map.values())) == len(left_map)
    assert len(set(right_map.values())) == len(right_map)
    return result, left_map, right_map


def inspect(mesh, expected=None):
    triangles = mesh.triangles
    assert all(len(set(t)) == 3 for t in triangles)
    vertices = {v for t in triangles for v in t}
    edges, incident, neighbors = defaultdict(list), defaultdict(list), defaultdict(set)
    for index, (a, b, c) in enumerate(triangles):
        for v in (a, b, c):
            incident[v].append(index)
        for u, v in ((a, b), (b, c), (c, a)):
            edges[edge(u, v)].append((u, v))
            neighbors[u].add(v)
            neighbors[v].add(u)
    assert all(len(p) <= 2 for p in edges.values())
    assert all(len(p) < 2 or p[0] == p[1][::-1] for p in edges.values())

    visited = {next(iter(vertices))}
    q = deque(visited)
    while q:
        for v in neighbors[q.popleft()]:
            if v not in visited:
                visited.add(v)
                q.append(v)
    assert visited == vertices

    loops, _ = boundary_loops(mesh)
    boundary = {v for loop in loops for v in loop}
    for v in vertices:
        link, link_edges = defaultdict(set), []
        for face_index in incident[v]:
            x, y = [z for z in triangles[face_index] if z != v]
            link[x].add(y)
            link[y].add(x)
            link_edges.append(edge(x, y))
        assert len(link_edges) == len(set(link_edges))
        assert all(1 <= len(ns) <= 2 for ns in link.values())
        reached = {next(iter(link))}
        q = deque(reached)
        while q:
            for z in link[q.popleft()]:
                if z not in reached:
                    reached.add(z)
                    q.append(z)
        assert len(reached) == len(link)
        endpoints = sum(len(ns) == 1 for ns in link.values())
        assert endpoints == (2 if v in boundary else 0), (v, endpoints)

    chi = len(vertices) - len(edges) + len(triangles)
    boundaries = len(loops)
    assert (2 - boundaries - chi) % 2 == 0
    genus = (2 - boundaries - chi) // 2
    assert genus >= 0
    result = dict(vertices=len(vertices), edges=len(edges),
                  triangles=len(triangles), boundaries=boundaries,
                  euler=chi, genus=genus, vertex_links_verified=True,
                  oriented=True, connected=True)
    if expected is not None:
        assert (genus, boundaries) == expected, (result, expected)
    return result


def audit(max_depth=4):
    pieces = {"disk": disk(), "annulus": sphere_with_holes(2),
              "pants": sphere_with_holes(3), "handle": torus_with_holes(2)}
    for name, want in (("disk", (0, 1)), ("annulus", (0, 2)),
                       ("pants", (0, 3)), ("handle", (1, 2))):
        inspect(pieces[name], want)
    families = {}
    for family in ("cantor", "loch", "jacob"):
        mesh = pieces["annulus"] if family == "jacob" else pieces["disk"]
        stages = []
        for n in range(max_depth + 1):
            want = ((0, 2 ** n) if family == "cantor" else
                    (n, 1) if family == "loch" else (2 * n, 2))
            stages.append(inspect(mesh, want))
            if n == max_depth:
                break
            if family == "cantor":
                # LEGACY MESH-INTEGRITY REGRESSION ONLY.
                # WARNING: glue(..., which_a=0) may select a newborn
                # boundary; the resulting stage's b=2^n does NOT
                # certify Cantor branching. For true parentage use
                # exotic_topology_pl_frontier_lineage.staged("cantor").
                for _ in range(len(boundary_loops(mesh)[0])):
                    mesh = glue(mesh, pieces["pants"])
            elif family == "loch":
                mesh = glue(mesh, pieces["handle"])
            else:
                mesh = glue(mesh, pieces["handle"])
                mesh = glue(mesh, pieces["handle"], 1)
        families[family] = stages
    return {"fixtures": {k: inspect(v) for k, v in pieces.items()},
            "families": families,
            "status": "FINITE PL GEOMETRY ONLY; Cantor ancestry is NOT checked here (use exotic_topology_pl_frontier_lineage.py); infinite topology OPEN"}


if __name__ == "__main__":
    print(json.dumps(audit(), sort_keys=True, indent=2))
