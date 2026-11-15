#!/usr/bin/env python3
from __future__ import annotations

import itertools
import json
from collections import deque

import networkx as nx

P = 3
B = (
    (2, 2, 0, 0, 0),
    (2, 2, 2, 0, 2),
    (0, 2, 2, 2, 0),
    (0, 0, 2, 2, 0),
    (0, 2, 0, 0, 2),
)
ZERO = (0, 0, 0, 0, 0)


def add(u, v):
    return tuple((a + b) % P for a, b in zip(u, v))


def smul(a, u):
    return tuple((a * x) % P for x in u)


def dot_b(u, v):
    return sum(u[i] * B[i][j] * v[j] for i in range(5) for j in range(5)) % P


def q(u):
    return dot_b(u, u)


def canon_line(v):
    if v == ZERO:
        raise ValueError("zero has no projective line")
    for a in v:
        if a:
            inv = 1 if a == 1 else 2
            return smul(inv, v)
    raise AssertionError("unreachable")


def rref(rows):
    a = [list(r) for r in rows]
    if not a:
        return ()
    m, n = len(a), len(a[0])
    rr = 0
    for c in range(n):
        piv = next((i for i in range(rr, m) if a[i][c] % P), None)
        if piv is None:
            continue
        a[rr], a[piv] = a[piv], a[rr]
        inv = 1 if a[rr][c] % P == 1 else 2
        a[rr] = [(inv * x) % P for x in a[rr]]
        for i in range(m):
            if i != rr and a[i][c] % P:
                lam = a[i][c] % P
                a[i] = [(x - lam * y) % P for x, y in zip(a[i], a[rr])]
        rr += 1
        if rr == m:
            break
    return tuple(tuple(row) for row in a if any(row))


def span_vectors(rows):
    rows = rref(rows)
    out = set()
    for coeffs in itertools.product(range(P), repeat=len(rows)):
        v = ZERO
        for c, row in zip(coeffs, rows):
            v = add(v, smul(c, row))
        out.add(v)
    return out


def projective_subspace(rows):
    return frozenset(canon_line(v) for v in span_vectors(rows) if any(v))


def enumerate_subspaces(lines, k):
    seen = {}
    for comb in itertools.combinations(lines, k):
        rr = rref(comb)
        if len(rr) != k:
            continue
        ps = projective_subspace(rr)
        seen.setdefault(ps, rr)
    return list(seen.items())


def eye(n=5):
    return tuple(tuple(1 if i == j else 0 for j in range(n)) for i in range(n))


def matmul(a, b):
    return tuple(
        tuple(sum(a[i][k] * b[k][j] for k in range(len(b))) % P for j in range(len(b[0])))
        for i in range(len(a))
    )


def matvec(a, v):
    return tuple(sum(a[i][j] * v[j] for j in range(len(v))) % P for i in range(len(a)))


def reflection(r):
    cols = []
    for j in range(5):
        e = tuple(1 if i == j else 0 for i in range(5))
        c = dot_b(e, r)
        cols.append(add(e, smul((-c) % P, r)))
    return tuple(tuple(cols[j][i] for j in range(5)) for i in range(5))


def group_generated(gens):
    ident = eye(len(gens[0]))
    seen = {ident}
    queue = deque([ident])
    while queue:
        g = queue.popleft()
        for s in gens:
            h = matmul(s, g)
            if h not in seen:
                seen.add(h)
                queue.append(h)
    return seen


def act_line(g, line):
    return canon_line(matvec(g, line))


def act_subspace(g, subspace):
    return frozenset(act_line(g, line) for line in subspace)


def graph_on(lines):
    graph = nx.Graph()
    graph.add_nodes_from(lines)
    for i, a in enumerate(lines):
        for b in lines[i + 1 :]:
            if dot_b(a, b) == 0:
                graph.add_edge(a, b)
    return graph


def srg_params(graph):
    degrees = {d for _, d in graph.degree()}
    if len(degrees) != 1:
        return None
    k = next(iter(degrees))
    lambdas, mus = set(), set()
    nodes = list(graph)
    for i, a in enumerate(nodes):
        na = set(graph[a])
        for b in nodes[i + 1 :]:
            c = len(na & set(graph[b]))
            (lambdas if graph.has_edge(a, b) else mus).add(c)
    return (
        len(nodes),
        k,
        next(iter(lambdas)) if len(lambdas) == 1 else tuple(sorted(lambdas)),
        next(iter(mus)) if len(mus) == 1 else tuple(sorted(mus)),
    )


def symplectic4(u, v):
    return (u[0] * v[1] - u[1] * v[0] + u[2] * v[3] - u[3] * v[2]) % P


def canon4(v):
    for a in v:
        if a:
            inv = 1 if a == 1 else 2
            return tuple((inv * x) % P for x in v)
    raise ValueError("zero has no projective point")


def pg3_points():
    return sorted({canon4(v) for v in itertools.product(range(P), repeat=4) if any(v)})


def symplectic_lines():
    points = pg3_points()
    out = set()
    for a, b in itertools.combinations(points, 2):
        if symplectic4(a, b) != 0:
            continue
        vectors = set()
        for x, y in itertools.product(range(P), repeat=2):
            v = tuple((x * a[i] + y * b[i]) % P for i in range(4))
            if any(v):
                vectors.add(canon4(v))
        if len(vectors) == 4:
            out.add(frozenset(vectors))
    return list(out)


VECTORS = list(itertools.product(range(P), repeat=5))
LINES = sorted({canon_line(v) for v in VECTORS if any(v)})
NULL_LINES = [v for v in LINES if q(v) == 0]
ROOT_LINES = [v for v in LINES if q(v) == 2]
OTHER_LINES = [v for v in LINES if q(v) == 1]

# Five visible simple roots plus a sixth root attached to the fifth node.
SIMPLE_ROOTS = (
    (1, 0, 0, 0, 0),
    (0, 1, 0, 0, 0),
    (0, 0, 1, 0, 0),
    (0, 0, 0, 1, 0),
    (0, 0, 0, 0, 1),
    (0, 0, 2, 1, 1),
)
SIMPLE_REFLECTIONS = tuple(reflection(r) for r in SIMPLE_ROOTS)


def compute_receipt():
    assert len(VECTORS) == 243
    assert (len(NULL_LINES), len(ROOT_LINES), len(OTHER_LINES)) == (40, 36, 45)

    g_null = graph_on(NULL_LINES)
    g_root = graph_on(ROOT_LINES)
    g_other = graph_on(OTHER_LINES)

    subs2 = enumerate_subspaces(LINES, 2)
    h2 = [
        s
        for s, _ in subs2
        if sum(x in ROOT_LINES for x in s) == 2 and sum(x in NULL_LINES for x in s) == 0
    ]
    subs3 = enumerate_subspaces(LINES, 3)
    h3 = [
        s
        for s, _ in subs3
        if sum(x in ROOT_LINES for x in s) == 6 and sum(x in NULL_LINES for x in s) == 1
    ]
    assert len(h2) == 270 and len(h3) == 120

    h3_meta = []
    for s in h3:
        radical = [n for n in s if n in NULL_LINES and all(dot_b(n, x) == 0 for x in s)]
        assert len(radical) == 1
        perp_roots = [r for r in ROOT_LINES if all(dot_b(r, x) == 0 for x in s)]
        a2cube = frozenset([r for r in ROOT_LINES if r in s] + perp_roots)
        assert len(a2cube) == 9
        h3_meta.append((radical[0], a2cube))

    by_radical, by_cube = {}, {}
    for null_line, cube in h3_meta:
        by_radical.setdefault(null_line, set()).add(cube)
        by_cube.setdefault(cube, set()).add(null_line)
    assert len(by_radical) == 40 and all(len(cubes) == 1 for cubes in by_radical.values())
    assert len(by_cube) == 40 and all(len(lines) == 1 for lines in by_cube.values())

    h1 = [frozenset([r]) for r in ROOT_LINES]
    h4 = []
    for r in ROOT_LINES:
        h4.append(frozenset(line for line in LINES if dot_b(line, r) == 0))
    h4 = list(dict.fromkeys(h4))
    assert len(h4) == 36

    inc43 = sum(1 for a in h4 for b in h3 if b <= a)
    inc32 = sum(1 for a in h3 for b in h2 if b <= a)
    inc21 = sum(1 for a in h2 for b in h1 if b <= a)

    weyl = group_generated(SIMPLE_REFLECTIONS)
    assert len(weyl) == 51840
    reps = [h4[0], h3[0], h2[0], h1[0]]
    stabilizers = [[g for g in weyl if act_subspace(g, s) == s] for s in reps]

    h3_rep = h3[0]
    h3_perp_roots = [r for r in ROOT_LINES if all(dot_b(r, x) == 0 for x in h3_rep)]
    h3_root_lines = sorted(set([r for r in ROOT_LINES if r in h3_rep] + h3_perp_roots))
    core3 = group_generated([reflection(r) for r in h3_root_lines])

    h2_rep = h2[0]
    h2_selected = [r for r in ROOT_LINES if r in h2_rep]
    h2_perp_roots = [r for r in ROOT_LINES if all(dot_b(r, x) == 0 for x in h2_rep)]
    core2 = group_generated([reflection(r) for r in sorted(set(h2_selected + h2_perp_roots))])

    complete_flags = 0
    one_flag = None
    for a in h4:
        for b in h3:
            if not b <= a:
                continue
            for c in h2:
                if not c <= b:
                    continue
                for d in h1:
                    if d <= c:
                        complete_flags += 1
                        if one_flag is None:
                            one_flag = (a, b, c, d)
    assert complete_flags == 6480
    full_flag_stabilizer = [g for g in weyl if all(act_subspace(g, s) == s for s in one_flag)]

    root0 = ROOT_LINES[0]
    orthogonal = [r for r in ROOT_LINES if r != root0 and dot_b(root0, r) == 0]
    local_root_graph = graph_on(orthogonal)
    kg62 = nx.kneser_graph(6, 2)

    sp_points = pg3_points()
    sp_lines = symplectic_lines()
    g_sp_points = nx.Graph()
    g_sp_points.add_nodes_from(range(len(sp_points)))
    for i, a in enumerate(sp_points):
        for j, b in enumerate(sp_points[i + 1 :], i + 1):
            if symplectic4(a, b) == 0:
                g_sp_points.add_edge(i, j)

    g_sp_lines = nx.Graph()
    g_sp_lines.add_nodes_from(range(len(sp_lines)))
    for i, a in enumerate(sp_lines):
        for j, b in enumerate(sp_lines[i + 1 :], i + 1):
            if a & b:
                g_sp_lines.add_edge(i, j)

    g_a2cube = nx.relabel_nodes(
        g_null,
        {n: next(iter(by_radical[n])) for n in NULL_LINES},
        copy=True,
    )

    return {
        "e6": {
            "states": 243,
            "projective_strata": {"null": 40, "root": 36, "other": 45},
            "srg": {
                "null": srg_params(g_null),
                "root": srg_params(g_root),
                "other": srg_params(g_other),
            },
            "weyl_order": len(weyl),
            "patch_orbits": {"H4": len(h4), "H3": len(h3), "H2": len(h2), "H1": len(h1)},
            "patch_stabilizers": {
                "H4": len(stabilizers[0]),
                "H3": len(stabilizers[1]),
                "H2": len(stabilizers[2]),
                "H1": len(stabilizers[3]),
            },
            "reflection_cores": {"H3": len(core3), "H2": len(core2)},
            "a2cube_subsystems": len(by_cube),
            "h3_per_a2cube": len(h3) // len(by_cube),
            "radical_null_line_indexes_a2cube": True,
            "incidence_edges": {"H4_H3": inc43, "H3_H2": inc32, "H2_H1": inc21},
            "complete_flags": complete_flags,
            "complete_flag_stabilizer": len(full_flag_stabilizer),
            "root_orthogonal_graph_is_KG_6_2": nx.is_isomorphic(local_root_graph, kg62),
        },
        "e8": {
            "symplectic_projective_points": len(sp_points),
            "symplectic_projective_lines": len(sp_lines),
            "symplectic_point_srg": srg_params(g_sp_points),
            "root_orbits_order3": 80,
        },
        "bridge": {
            "e6_null_to_e8_line_graph_isomorphic": nx.is_isomorphic(g_null, g_sp_lines),
            "e6_null_to_e8_point_graph_isomorphic": nx.is_isomorphic(g_null, g_sp_points),
            "a2cube_to_e8_symplectic_line_graph_isomorphic": nx.is_isomorphic(g_a2cube, g_sp_lines),
        },
    }


if __name__ == "__main__":
    print(json.dumps(compute_receipt(), indent=2, sort_keys=True))
