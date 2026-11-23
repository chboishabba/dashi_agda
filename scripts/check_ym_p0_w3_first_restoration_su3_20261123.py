#!/usr/bin/env python3
"""Original L4 4D Wilson W3 eight-wall first missing-plaquette restoration.

Full original link/plaquette incidence and exact SU(3) Haar epsilon network.
No finite-subgroup replacement, MC, Agda or continuum mass gap claim.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, product
from math import factorial

L = 4
def step(x, mu):
    y = list(x)
    y[mu] = (y[mu] + 1) % L
    return tuple(y)

def plaquette(x, mu, nu):
    return (x, mu, nu) if mu < nu else (x, nu, mu)

def edges(p):
    x, mu, nu = p
    return (
        ((x, mu), 1),
        ((step(x, mu), nu), 1),
        ((step(x, nu), mu), -1),
        ((x, nu), -1),
    )

all_faces = [plaquette(x, mu, nu)
    for x in product(range(L), repeat=4)
    for mu, nu in combinations(range(4), 2)]
F = plaquette((0, 0, 0, 0), 1, 2)
G = plaquette((2, 0, 0, 0), 1, 2)
M = plaquette((1, 0, 0, 0), 1, 2)
walls = [
    plaquette((t, 0, 0, 0), 0, 1) for t in (0, 1)
] + [
    plaquette((t, 0, 1, 0), 0, 1) for t in (0, 1)
] + [
    plaquette((t, 0, 0, 0), 0, 2) for t in (0, 1)
] + [
    plaquette((t, 1, 0, 0), 0, 2) for t in (0, 1)
]
base_faces = [F, G] + walls
assert len(all_faces) == 1536 and len(set(walls)) == 8
base_links = Counter(link for face in base_faces for link, _ in edges(face))
assert len(base_links) == 20 and set(base_links.values()) == {2}
omitted = [face for face in all_faces if face not in walls]
assert len(omitted) == 1528
overlap = Counter(
    sum(link in base_links for link, _ in edges(face))
    for face in omitted
)
assert overlap == {0: 1449, 1: 76, 4: 3}, overlap
exceptional = [face for face in omitted
    if all(link in base_links for link, _ in edges(face))]
assert set(exceptional) == {F, M, G}
print("PASS full original geometry: 1536 faces, 1024 links, 8 walls, 1528 omitted")
print("PASS omitted-face overlap histogram", dict(overlap), "; exceptions: F, M, G")

def all_link_occurrences(faces):
    result = defaultdict(list)
    for i, face in enumerate(faces):
        for link, sign in edges(face):
            result[link].append((i, sign))
    return result

def neutral_orientations(faces, N):
    occ = all_link_occurrences(faces)
    out = []
    for mask in range(1 << len(faces)):
        ori = [1 if (mask >> i) & 1 else -1 for i in range(len(faces))]
        if all(sum(ori[i] * sign for i, sign in appearances) % N == 0
               for appearances in occ.values()):
            out.append(ori)
    return out

def index_graph_for_su3(faces):
    occ = all_link_occurrences(faces)
    variables = {}
    def ix(i, x):
        if (i, x) not in variables:
            variables[i, x] = len(variables)
        return variables[i, x]
    for i, (x, mu, nu) in enumerate(faces):
        for site in (x, step(x, mu), step(step(x, mu), nu), step(x, nu)):
            ix(i, site)
    parent = list(range(len(variables)))
    def find(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i
    def union(a, b):
        parent[find(a)] = find(b)

    baryon = []
    double_count = 0
    for (x, d), users in occ.items():
        if len(users) == 2:
            i, j = [k for k, _ in users]
            union(ix(i, x), ix(j, x))
            union(ix(i, step(x, d)), ix(j, step(x, d)))
            double_count += 1
        elif len(users) == 3:
            baryon.append([
                [ix(i, x) for i, _ in users],
                [ix(i, step(x, d)) for i, _ in users],
            ])
        else:
            raise AssertionError("non-2/3 occupied link")
    roots = sorted({find(k) for k in range(len(variables))})
    reindex = {root: i for i, root in enumerate(roots)}
    epsilon_nodes = [
        [reindex[find(k)] for k in trip]
        for edge in baryon for trip in edge
    ]
    active = sorted({k for trip in epsilon_nodes for k in trip})
    index = {k: i for i, k in enumerate(active)}
    active_nodes = [[index[k] for k in trip] for trip in epsilon_nodes]
    assert double_count == 16 and len(baryon) == 4
    assert len(roots) == 20 and len(active) == 12
    return len(roots), len(active), active_nodes

def independent_levi_enumeration(nodes, size):
    # Exhaustively sum eight Levi-Civita signs on the 12 surviving color indices.
    # All 8 other Kronecker-equivalence classes are unconstrained: 3^8.
    positive = {(0, 1, 2), (1, 2, 0), (2, 0, 1)}
    signed_sum = nonzero = 0
    for colors in product((0, 1, 2), repeat=size):
        sign = 1
        for node in nodes:
            trip = tuple(colors[index] for index in node)
            if len(set(trip)) != 3:
                sign = 0
                break
            if trip not in positive:
                sign = -sign
        signed_sum += sign
        if sign:
            nonzero += 1
    return signed_sum, nonzero

def irreducible_under_singleton_link(faces):
    # Every proper partition into nonempty families has at least one
    # subset with a singly occupied original link -> Haar moment zero.
    total = (1 << len(faces)) - 1
    support = [[link for link, _ in edges(face)] for face in faces]
    for mask in range(1, total):
        def no_singleton(test_mask):
            counter = Counter(link for i, e in enumerate(support)
                              if (test_mask >> i) & 1 for link in e)
            return 1 not in counter.values()
        if no_singleton(mask) and no_singleton(total ^ mask):
            return False
    return True

original_su3_tube = Fraction(1, 2**9 * 3**18)
restoration = Fraction(1, 2**10 * 3**19)
assert restoration == original_su3_tube / 6

for H in exceptional:
    faces = base_faces + [H]
    assert irreducible_under_singleton_link(faces)
    assert len(neutral_orientations(faces, 2)) == 0
    assert len(neutral_orientations(faces, 3)) == 2
    for N in (4, 5, 6):
        assert len(neutral_orientations(faces, N)) == 0
    roots, active, nodes = index_graph_for_su3(faces)
    signed, nonzero = independent_levi_enumeration(nodes, active)
    assert (signed, nonzero) == (6**4, 6**4)
    # 16 two-entry Haar links -> (1/3)^16;
    # 4 three-entry Haar links -> (1/6)^4;
    # all 11 ReTr/N faces -> (1/(2*3))^11;
    # 2 allowed orientations, 3^8 free index loops.
    moment = Fraction(
        2 * signed * 3**(roots-active),
        2**11 * 3**(11+16) * 6**4,
    )
    assert moment == restoration
    print("PASS original SU3 epsilon/Haar first restoration", H, moment)

assert 3 * restoration == original_su3_tube / 2
print("PASS SU2 and SU(N>=4) full omitted first-restoration jet = 0 (centre selection)")
print("PASS SU3 three-plaquette sum =", 3 * restoration,
      "= one-half original eighth tube coefficient", original_su3_tube)
print("TRUST: exact native multivariate zero-coupling coefficient only.")
print("NOT: full homogeneous-beta coefficient, CMP119/122 T, W3 absolute tail, OS gap.")
