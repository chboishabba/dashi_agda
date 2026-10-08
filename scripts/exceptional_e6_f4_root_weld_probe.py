from __future__ import annotations

from collections import Counter, defaultdict
from itertools import combinations_with_replacement, permutations, product
import numpy as np
import sympy as sp

from scripts.exceptional_f4_derivation_maxcut_probe import (
    BASIS,
    I3,
    P,
    cross3,
    jprod3,
    rank_mod3,
)


def rank_mod_p(matrix, p):
    a = np.asarray(matrix, dtype=np.int64).copy() % p
    m, n = a.shape
    rank = 0
    for col in range(n):
        pivots = np.flatnonzero(a[rank:, col])
        if pivots.size == 0:
            continue
        pivot = rank + int(pivots[0])
        if pivot != rank:
            a[[rank, pivot]] = a[[pivot, rank]]
        a[rank] = a[rank] * pow(int(a[rank, col]), -1, p) % p
        nz = np.flatnonzero(a[rank + 1 :, col])
        if nz.size:
            rows = nz + rank + 1
            factors = a[rows, col].copy()
            a[rows] = (a[rows] - factors[:, None] * a[rank]) % p
        rank += 1
        if rank == m:
            break
    return rank


def determinant_parity(perm):
    inversions = sum(
        1
        for i in range(len(perm))
        for j in range(i + 1, len(perm))
        if perm[i] > perm[j]
    )
    return -1 if inversions % 2 else 1


def cubic_terms():
    """N(X,Y,Z)=det X+det Y+det Z-tr(XYZ) as 45 cubic monomials."""
    terms = defaultdict(int)
    for base in (0, 9, 18):
        for perm in permutations(range(3)):
            mon = tuple(sorted(base + 3 * i + perm[i] for i in range(3)))
            terms[mon] += determinant_parity(perm)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                mon = tuple(sorted((3 * i + j, 9 + 3 * j + k, 18 + 3 * k + i)))
                terms[mon] -= 1
    return {mon: coeff for mon, coeff in terms.items() if coeff}


def cubic_invariance_matrix():
    """Deterministic infinitesimal invariance equations dN_x(Dx)=0."""
    monomials = list(combinations_with_replacement(range(27), 3))
    mon_index = {mon: i for i, mon in enumerate(monomials)}
    matrix = np.zeros((len(monomials), 729), dtype=np.int16)
    for mon, coeff in cubic_terms().items():
        factors = list(mon)
        for pos, output_coordinate in enumerate(factors):
            others = factors[:pos] + factors[pos + 1 :]
            for input_coordinate in range(27):
                target = tuple(sorted(others + [input_coordinate]))
                matrix[mon_index[target], output_coordinate * 27 + input_coordinate] += coeff
    return matrix[np.any(matrix != 0, axis=1)]


def unit_fixing_matrix():
    unit = np.zeros(27, dtype=int)
    unit[[0, 4, 8]] = 1
    rows = np.zeros((27, 729), dtype=int)
    for output in range(27):
        for input_coordinate in np.flatnonzero(unit):
            rows[output, output * 27 + input_coordinate] = 1
    return rows


def first_tits_structure_constants_mod(p):
    inv2 = pow(2, -1, p)
    identity = np.eye(3, dtype=np.int64) % p

    def tr(a):
        return int(np.trace(a) % p)

    def bullet(a, b):
        return inv2 * (a @ b + b @ a) % p

    def bar(a):
        return inv2 * (tr(a) * identity - a) % p

    def cross(a, b):
        ab = bullet(a, b)
        return (
            ab
            - inv2 * tr(a) * b
            - inv2 * tr(b) * a
            + inv2 * (tr(a) * tr(b) - tr(ab)) * identity
        ) % p

    def product_j(x, y):
        a, b, c = x
        d, e, f = y
        return (
            (bullet(a, d) + bar(b @ f) + bar(e @ c)) % p,
            (bar(a) @ e + bar(d) @ b + cross(c, f)) % p,
            (f @ bar(a) + c @ bar(d) + cross(b, e)) % p,
        )

    basis = []
    for s in range(3):
        for i in range(3):
            for j in range(3):
                out = [np.zeros((3, 3), dtype=np.int64) for _ in range(3)]
                out[s][i, j] = 1
                basis.append(tuple(out))

    constants = np.zeros((27, 27, 27), dtype=np.int64)
    for i, x in enumerate(basis):
        for j, y in enumerate(basis):
            v = np.concatenate([block.reshape(-1) for block in product_j(x, y)]) % p
            constants[:, i, j] = v
    return constants


def derivation_matrix_mod(p):
    c = first_tits_structure_constants_mod(p)
    rows = []
    for i in range(27):
        for j in range(i, 27):
            support = np.flatnonzero(c[:, i, j])
            for k in range(27):
                row = np.zeros(729, dtype=np.int64)
                for l in support:
                    row[k * 27 + l] = (row[k * 27 + l] + c[l, i, j]) % p
                for a in np.flatnonzero(c[k, :, j]):
                    row[a * 27 + i] = (row[a * 27 + i] - c[k, a, j]) % p
                for b in np.flatnonzero(c[k, i, :]):
                    row[b * 27 + j] = (row[b * 27 + j] - c[k, i, b]) % p
                if np.any(row):
                    rows.append(row)
    return np.asarray(rows, dtype=np.int64) % p


def representation_weights_a2_cubed():
    h1 = (1, -1, 0)
    h2 = (0, 1, -1)
    weights = []
    labels = []
    for i in range(3):
        for j in range(3):
            weights.append((h1[i], h2[i], -h1[j], -h2[j], 0, 0))
            labels.append(("X", i, j))
    for i in range(3):
        for j in range(3):
            weights.append((0, 0, h1[i], h2[i], -h1[j], -h2[j]))
            labels.append(("Y", i, j))
    for i in range(3):
        for j in range(3):
            weights.append((-h1[j], -h2[j], 0, 0, h1[i], h2[i]))
            labels.append(("Z", i, j))
    return weights, labels


def e6_root_weights(norm_matrix, p=101):
    weights, _ = representation_weights_a2_cubed()
    weight_columns = defaultdict(list)
    for output in range(27):
        for input_coordinate in range(27):
            weight = tuple(weights[output][k] - weights[input_coordinate][k] for k in range(6))
            weight_columns[weight].append(output * 27 + input_coordinate)

    multiplicities = {}
    for weight, columns in weight_columns.items():
        nullity = len(columns) - rank_mod_p(norm_matrix[:, columns], p)
        if nullity:
            multiplicities[weight] = nullity
    return multiplicities


def simple_roots_from_positive(roots, functional):
    roots = [tuple(map(int, r)) for r in roots]
    positive = [r for r in roots if sum(r[i] * functional[i] for i in range(len(r))) > 0]
    positive_set = set(positive)
    simple = []
    for root in positive:
        if not any(
            tuple(root[i] - other[i] for i in range(len(root))) in positive_set
            for other in positive
        ):
            simple.append(root)
    return simple


def cartan_from_root_strings(roots, simple):
    root_set = set(roots)

    def shift(beta, alpha, n):
        return tuple(beta[i] + n * alpha[i] for i in range(len(beta)))

    matrix = np.zeros((len(simple), len(simple)), dtype=int)
    for i, alpha in enumerate(simple):
        for j, beta in enumerate(simple):
            if i == j:
                matrix[i, j] = 2
                continue
            p = 0
            while shift(beta, alpha, -(p + 1)) in root_set:
                p += 1
            q = 0
            while shift(beta, alpha, q + 1) in root_set:
                q += 1
            matrix[i, j] = p - q
    return matrix


def minuscule_weight_graph(e6_roots):
    weights, _ = representation_weights_a2_cubed()
    roots = set(e6_roots)
    adjacency = np.zeros((27, 27), dtype=int)
    for i, left in enumerate(weights):
        for j, right in enumerate(weights):
            if i != j:
                difference = tuple(left[k] - right[k] for k in range(6))
                adjacency[i, j] = int(difference in roots)
    degrees = Counter(map(int, adjacency.sum(axis=1)))
    adjacent_common = Counter()
    nonadjacent_common = Counter()
    for i in range(27):
        for j in range(i + 1, 27):
            common = int(np.dot(adjacency[i], adjacency[j]))
            (adjacent_common if adjacency[i, j] else nonadjacent_common)[common] += 1
    return degrees, adjacent_common, nonadjacent_common


def rational_f4_root_weld():
    half = sp.Rational(1, 2)
    identity = sp.eye(3)

    def tr(a):
        return sp.trace(a)

    def bullet(a, b):
        return half * (a * b + b * a)

    def bar(a):
        return half * (tr(a) * identity - a)

    def cross(a, b):
        ab = bullet(a, b)
        return (
            ab - half * tr(a) * b - half * tr(b) * a
            + half * (tr(a) * tr(b) - tr(ab)) * identity
        )

    def jp(x, y):
        a, b, c = x
        d, e, f = y
        return (
            bullet(a, d) + bar(b * f) + bar(e * c),
            bar(a) * e + bar(d) * b + cross(c, f),
            f * bar(a) + c * bar(d) + cross(b, e),
        )

    basis = []
    for s in range(3):
        for i in range(3):
            for j in range(3):
                mats = [sp.zeros(3) for _ in range(3)]
                mats[s][i, j] = 1
                basis.append(tuple(mats))

    def flatten(x):
        values = []
        for block in x:
            values += list(block)
        return sp.Matrix(values)

    left = []
    for x in basis:
        matrix = sp.zeros(27)
        for j, y in enumerate(basis):
            matrix[:, j] = flatten(jp(x, y))
        left.append(matrix)

    inner = []
    for i in range(27):
        for j in range(i + 1, 27):
            d = left[i] * left[j] - left[j] * left[i]
            if d != sp.zeros(27):
                inner.append(d)

    flat_inner = sp.Matrix.hstack(*[d.reshape(729, 1) for d in inner]).T
    independent = flat_inner.T.rref()[1]
    derivations = [inner[i] for i in independent]
    basis_matrix = sp.Matrix.hstack(*[d.reshape(729, 1) for d in derivations])
    coordinate_rows = basis_matrix.T.rref()[1]
    selector = basis_matrix[list(coordinate_rows), :]
    selector_inverse = selector.inv()

    def coordinates(d):
        v = d.reshape(729, 1)
        return selector_inverse * v[list(coordinate_rows), :]

    h1 = sp.diag(1, -1, 0)
    h2 = sp.diag(0, 1, -1)

    def infinitesimal(p, q):
        d = sp.zeros(27)
        for j, (x, y, z) in enumerate(basis):
            out = (p * x - x * p, p * y - y * q, q * z - z * p)
            d[:, j] = flatten(out)
        return d

    cartan_derivations = [
        infinitesimal(h1, sp.zeros(3)),
        infinitesimal(h2, sp.zeros(3)),
        infinitesimal(sp.zeros(3), h1),
        infinitesimal(sp.zeros(3), h2),
    ]

    ad = []
    for h in cartan_derivations:
        matrix = sp.zeros(52)
        for j, d in enumerate(derivations):
            matrix[:, j] = coordinates(h * d - d * h)
        ad.append(matrix)

    generic = ad[0] + 10 * ad[1] + 100 * ad[2] + 1000 * ad[3]
    weights = []
    for _, _, vectors in generic.eigenvects():
        for vector in vectors:
            pivot = next(i for i, value in enumerate(vector) if value != 0)
            weight = []
            for action in ad:
                image = action * vector
                scalar = sp.simplify(image[pivot] / vector[pivot])
                assert image == scalar * vector
                weight.append(int(scalar))
            weights.append(tuple(weight))

    multiplicities = Counter(weights)
    roots = sorted(weight for weight in multiplicities if weight != (0, 0, 0, 0))
    killing = sp.Matrix(4, 4, lambda i, j: sp.trace(ad[i] * ad[j]))
    metric = killing.inv()
    lengths = Counter(
        sp.simplify((sp.Matrix(root).T * metric * sp.Matrix(root))[0])
        for root in roots
    )

    simple = simple_roots_from_positive(roots, (1, 10, 100, 1000))
    simple = [simple[i] for i in (2, 1, 3, 0)]
    cartan = sp.Matrix(4, 4, lambda i, j:
        sp.simplify(
            2 * (sp.Matrix(simple[i]).T * metric * sp.Matrix(simple[j]))[0]
            / (sp.Matrix(simple[j]).T * metric * sp.Matrix(simple[j]))[0]
        )
    )

    repo_simple = [
        sp.Matrix((0, 2, -2, 0)),
        sp.Matrix((0, 0, 2, -2)),
        sp.Matrix((0, 0, 0, 2)),
        sp.Matrix((1, -1, -1, -1)),
    ]
    source_simple = [sp.Matrix(root) for root in simple]
    weld = sp.Matrix.hstack(*repo_simple) * sp.Matrix.hstack(*source_simple).inv()

    repo_roots = set()
    for i in range(4):
        for sign in (-1, 1):
            vector = [0] * 4
            vector[i] = 2 * sign
            repo_roots.add(tuple(vector))
    for i in range(4):
        for j in range(i + 1, 4):
            for left_sign in (-1, 1):
                for right_sign in (-1, 1):
                    vector = [0] * 4
                    vector[i] = 2 * left_sign
                    vector[j] = 2 * right_sign
                    repo_roots.add(tuple(vector))
    repo_roots.update(product((-1, 1), repeat=4))

    mapped = {
        tuple(int(value) for value in weld * sp.Matrix(root))
        for root in roots
    }
    assert mapped == repo_roots
    assert sp.simplify(weld.T * weld - 72 * metric) == sp.zeros(4)

    return {
        "dimension": len(derivations),
        "cartan_multiplicity": multiplicities[(0, 0, 0, 0)],
        "root_count": len(roots),
        "root_multiplicities": Counter(multiplicities[root] for root in roots),
        "root_lengths": lengths,
        "cartan": cartan,
        "weld": weld,
        "root_sets_equal": mapped == repo_roots,
        "metric_scale": 72,
    }


def verify():
    norm = cubic_invariance_matrix()
    assert len(cubic_terms()) == 45
    assert norm.shape == (2475, 729)
    norm_ranks = {prime: rank_mod_p(norm, prime) for prime in (5, 7, 101)}
    assert norm_ranks == {5: 651, 7: 651, 101: 651}
    assert 729 - norm_ranks[101] == 78

    unit = unit_fixing_matrix()
    unit_stabilizer_rank = rank_mod_p(np.vstack((norm, unit)), 101)
    assert unit_stabilizer_rank == 677
    assert 729 - unit_stabilizer_rank == 52

    derivation = derivation_matrix_mod(101)
    derivation_rank = rank_mod_p(derivation, 101)
    assert derivation_rank == 677
    same_subspace_rank = rank_mod_p(np.vstack((norm, unit, derivation)), 101)
    assert same_subspace_rank == 677

    multiplicities = e6_root_weights(norm, 101)
    zero = (0, 0, 0, 0, 0, 0)
    assert multiplicities[zero] == 6
    e6_roots = sorted(weight for weight in multiplicities if weight != zero)
    assert len(e6_roots) == 72
    assert all(multiplicities[root] == 1 for root in e6_roots)

    simple = simple_roots_from_positive(e6_roots, (1, 7, 49, 343, 2401, 16807))
    assert len(simple) == 6
    cartan = cartan_from_root_strings(set(e6_roots), simple)
    order = (0, 2, 4, 1, 3, 5)
    cartan_reordered = cartan[np.ix_(order, order)]
    expected_e6 = np.array([
        [2, -1, 0, 0, 0, 0],
        [-1, 2, -1, 0, 0, 0],
        [0, -1, 2, -1, 0, -1],
        [0, 0, -1, 2, -1, 0],
        [0, 0, 0, -1, 2, 0],
        [0, 0, -1, 0, 0, 2],
    ])
    assert np.array_equal(cartan_reordered, expected_e6)
    assert round(np.linalg.det(cartan_reordered)) == 3

    degree, adjacent_common, nonadjacent_common = minuscule_weight_graph(e6_roots)
    assert degree == Counter({16: 27})
    assert adjacent_common == Counter({10: 216})
    assert nonadjacent_common == Counter({8: 135})

    f4 = rational_f4_root_weld()
    expected_f4 = sp.Matrix([
        [2, -1, 0, 0],
        [-1, 2, -2, 0],
        [0, -1, 2, -1],
        [0, 0, -1, 2],
    ])
    assert f4["dimension"] == 52
    assert f4["cartan_multiplicity"] == 4
    assert f4["root_count"] == 48
    assert f4["root_multiplicities"] == Counter({1: 48})
    assert f4["root_lengths"] == Counter({sp.Rational(1, 9): 24, sp.Rational(1, 18): 24})
    assert f4["cartan"] == expected_f4
    assert f4["root_sets_equal"]

    return {
        "cubic_monomial_count": len(cubic_terms()),
        "norm_symmetry_rank": norm_ranks[101],
        "norm_symmetry_dimension": 78,
        "unit_stabilizer_rank": unit_stabilizer_rank,
        "unit_stabilizer_dimension": 52,
        "derivation_rank": derivation_rank,
        "derivation_dimension": 52,
        "unit_stabilizer_equals_derivations_mod101": same_subspace_rank == 677,
        "e6_cartan_dimension": multiplicities[zero],
        "e6_root_count": len(e6_roots),
        "e6_cartan": cartan_reordered.tolist(),
        "minuscule_srg": (27, 16, 10, 8),
        "f4_cartan_dimension": f4["cartan_multiplicity"],
        "f4_root_count": f4["root_count"],
        "f4_short_long_counts": (24, 24),
        "f4_cartan": [list(map(int, f4["cartan"].row(i))) for i in range(4)],
        "f4_repo_root_set_weld": f4["root_sets_equal"],
        "f4_metric_scale": f4["metric_scale"],
        "f4_weld_matrix": f4["weld"],
    }


if __name__ == "__main__":
    for key, value in verify().items():
        print(f"{key}: {value}")
