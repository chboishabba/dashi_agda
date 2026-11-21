#!/usr/bin/env python3
"""Local SymPy acceptance for original F19/R445 -> native 64-link finite square.

Original 4D side-four fine 1024 positive Wilson bonds; original side-two
coarse 64 bonds; 128 ordered selected fine links + 896 spectators.
SymPy exact noncommutative words and exact Q8 subgroup of SU(2).
No Agda/CI, continuum OS/H, Wilson-Gibbs or physical decay claim.
"""
from itertools import product, combinations
import sympy as sp
from sympy.combinatorics import Permutation

def bonds(side):
    return tuple((site, axis) for site in product(range(side), repeat=4)
                 for axis in range(4))

def step(site, axis, side):
    out = list(site)
    out[axis] = (out[axis] + 1) % side
    return tuple(out)

def native_pair(site, axis):
    origin = tuple(2 * x for x in site)
    return (origin, axis), (step(origin, axis, 4), axis)

def plaquette(field, site, a, b, side):
    return sp.Mul(field[(site, a)], field[(step(site, a, side), b)],
                  sp.Pow(field[(step(site, b, side), a)], -1, evaluate=False),
                  sp.Pow(field[(site, b)], -1, evaluate=False), evaluate=False)

fine = bonds(4)
coarse = bonds(2)
pos = {v: i for i, v in enumerate(fine)}
assert len(fine) == len(pos) == 1024 and len(coarse) == 64

# Independent linear Boolean filter and set-based selected mask as in
# F19's original target and the R445 original canonical residual codec.
selected_f19 = tuple(link for site, a in coarse for link in native_pair(site, a))
selected_r445 = tuple(native_pair(site, a)[phase]
                      for site, a in coarse for phase in (0, 1))
assert selected_f19 == selected_r445 and len(set(selected_f19)) == 128
spectators_f19 = tuple(link for link in fine
                       if all(link != s for s in selected_f19))
selected_set = set(selected_r445)
spectators_r445 = tuple(link for link in fine if link not in selected_set)
assert spectators_f19 == spectators_r445 and len(spectators_r445) == 896
target = selected_f19 + spectators_f19
assert len(target) == len(set(target)) == 1024
index = tuple(pos[b] for b in target)
permutation = Permutation(index)
assert permutation * ~permutation == Permutation(list(range(1024)))
assert ~permutation * permutation == Permutation(list(range(1024)))
inverse = [None] * 1024
for j, i in enumerate(index):
    assert inverse[i] is None
    inverse[i] = j
assert all(inverse[index[j]] == j for j in range(1024))
assert all(index[inverse[i]] == i for i in range(1024))

# UNIVERSAL non-Abelian identity: the symbolic variables are explicitly
# noncommutative and each original native link comes from its actual bond.
U = tuple(sp.Symbol("U" + str(i), commutative=False) for i in range(1024))
field = dict(zip(fine, U))
sorted_values = tuple(U[i] for i in index)
native = {bond: sp.Mul(*(field[b] for b in native_pair(*bond)),
                       evaluate=False) for bond in coarse}
f19 = {bond: sp.Mul(sorted_values[2*j], sorted_values[2*j+1],
                    evaluate=False) for j, bond in enumerate(coarse)}
assert all(native[b] == f19[b] for b in coarse)
assert [sorted_values[inverse[i]] for i in range(1024)] == list(U)
word_checks = 0
for site in product(range(2), repeat=4):
    for a, b in combinations(range(4), 2):
        assert plaquette(native, site, a, b, 2) == plaquette(f19, site, a, b, 2)
        word_checks += 1
assert word_checks == 96

# Exact SU(2) quaternion matrix subgroup, not floating-point sampling.
I = sp.I
one = sp.eye(2)
i = sp.diag(I, -I)
j = sp.Matrix([[0, 1], [-1, 0]])
k = i*j
q8 = (one, -one, i, -i, j, -j, k, -k)
assert all(m*m.conjugate().T == one and sp.simplify(m.det()) == 1 for m in q8)
matrix_links = matrix_blocks = matrix_plaquettes = reverse_diffs = spectators = 0
for sample in range(5):
    values = tuple(q8[(13*n + sample*23 +
                       sum((5, 11, 17, 19)[z]*v for z, v in enumerate(site)) +
                       axis*7) % 8] for n, (site, axis) in enumerate(fine))
    original = dict(zip(fine, values))
    arranged = [values[index[z]] for z in range(1024)]
    assert all(arranged[inverse[n]] == values[n] for n in range(1024))
    matrix_links += 1024
    native_values = {}
    f19_values = {}
    for p, bond in enumerate(coarse):
        first, second = native_pair(*bond)
        native_values[bond] = original[first]*original[second]
        f19_values[bond] = arranged[2*p]*arranged[2*p+1]
        assert native_values[bond] == f19_values[bond]
        reverse_diffs += (native_values[bond] != original[second]*original[first])
        matrix_blocks += 1
    for site in product(range(2), repeat=4):
        for a, b in combinations(range(4), 2):
            def tr(field):
                w = field[(site, a)]*field[(step(site, a, 2), b)]
                w = w*field[(step(site, b, 2), a)].conjugate().T
                return sp.trace(w*field[(site, b)].conjugate().T)
            assert tr(native_values) == tr(f19_values)
            matrix_plaquettes += 1
    bond = spectators_f19[128+sample]
    altered = dict(original)
    altered[bond] = -altered[bond]
    assert all(altered[x]*altered[y] == native_values[c]
               for c in coarse for x, y in (native_pair(*c),))
    site, a = bond
    b = (a+1) % 4
    replaced = dict(field)
    replaced[bond] = sp.Symbol("modified_spectator", commutative=False)
    assert plaquette(field, site, a, b, 4) != plaquette(replaced, site, a, b, 4)
    spectators += 1
assert (matrix_links, matrix_blocks, matrix_plaquettes, spectators) == \
       (5120, 320, 480, 5)
assert reverse_diffs > 0
print("SymPy", sp.__version__)
print("PASS complete original 1024-link F19/R445 perm and both inverses")
print("PASS exact noncommutative native/F19 block: 64/64")
print("PASS exact noncommutative coarse plaquette words: 96/96")
print("PASS exact SU2 Q8 link values: 5120/5120")
print("PASS exact SU2 Q8 native ordered block: 320/320")
print("PASS exact SU2 Q8 coarse plaquette traces: 480/480")
print("NEGATIVE reversed SU2 link products differ:", reverse_diffs)
print("NEGATIVE spectators affect original fine words, not blocks: 5/5")
print("OPEN Agda kernel, real interacting E1, original W1/W3, OS same-H gap")


# EXHAUSTIVE original fine Wilson plaquette incidence audit, not an
# inferred factorization of the interacting 1024-link Gibbs weight.
# Every one of the 896 unselected links remains a six-plaquette fine
# action variable even though it does not enter the 64 chosen blocks.
from collections import Counter
incidence = Counter()
plaquettes = 0
for site in product(range(4), repeat=4):
    for a, b in combinations(range(4), 2):
        edges = ((site, a), (step(site, a, 4), b),
                 (step(site, b, 4), a), (site, b))
        assert len(set(edges)) == 4
        incidence.update(edges)
        plaquettes += 1
assert plaquettes == 1536 and len(incidence) == 1024
assert all(incidence[b] == 6 for b in fine)
assert sum(incidence[b] for b in spectators_f19) == 5376
assert sum(incidence[b] for b in selected_f19) == 768
print("PASS original fine Wilson plaquettes: 1536")
print("PASS each original fine positive link has 6 plaquette incidences")
print("PASS all 896 original spectators retain 5376 fine-action incidences")
