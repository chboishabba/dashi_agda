#!/usr/bin/env python3
"""Exact finite audit of cubic-preserving monomial lifts of E6 simple reflections.

Starts from the already-paid E8->E6 minuscule 27 / first-Tits M3^3 basis-label
bridge.  The first-Tits cubic is

    N(X,Y,Z) = det X + det Y + det Z - tr(XYZ).

For each true E6 simple reflection, the transported permutation of the 27 weight
labels preserves the support of the 45 cubic monomials.  We solve over F2 for
signs eps_i in {+1,-1} such that

    e_i |-> eps_i e_{p(i)}

preserves every cubic coefficient exactly.

The resulting lifts are NOT asserted to give a strict section of W(E6).  Their
squares / Coxeter words can close by diagonal cubic-preserving 2-torsion, which
is the expected Weyl-normalizer / Tits-extension phenomenon.  The script emits
those residual diagonal receipts explicitly rather than collapsing them.
"""
from collections import Counter, defaultdict
from itertools import permutations, product

from check_e6_minuscule_first_tits_basis_bridge import (
    e6_side, first_tits_side, find_iso,
)


def determinant_parity(perm):
    inv = sum(1 for i in range(len(perm)) for j in range(i + 1, len(perm)) if perm[i] > perm[j])
    return -1 if inv % 2 else 1


def cubic_terms():
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
    return {m: c for m, c in terms.items() if c}


def solve_f2(masks, rhs, n):
    rows = [[(mask >> i) & 1 for i in range(n)] + [b] for mask, b in zip(masks, rhs)]
    r = 0
    pivots = []
    for c in range(n):
        p = next((i for i in range(r, len(rows)) if rows[i][c]), None)
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i][c]:
                rows[i] = [x ^ y for x, y in zip(rows[i], rows[r])]
        pivots.append(c)
        r += 1
    for row in rows:
        if not any(row[:n]) and row[n]:
            return None, None
    x = [0] * n
    for row, c in enumerate(pivots):
        x[c] = rows[row][n]
    return x, n - len(pivots)


def sign_lift(permutation, terms):
    masks, rhs = [], []
    for mon, coeff in terms.items():
        target = tuple(sorted(permutation[i] for i in mon))
        target_coeff = terms[target]
        mask = 0
        for i in mon:
            mask ^= 1 << i
        masks.append(mask)
        rhs.append(0 if target_coeff == coeff else 1)
    bits, nullity = solve_f2(masks, rhs, 27)
    assert bits is not None
    signs = tuple(-1 if b else 1 for b in bits)
    return signs, nullity


def signed_compose(left, right):
    p, s = left
    q, t = right
    return (
        tuple(p[q[i]] for i in range(27)),
        tuple(t[i] * s[q[i]] for i in range(27)),
    )


def signed_power(g, n):
    out = (tuple(range(27)), (1,) * 27)
    for _ in range(n):
        out = signed_compose(g, out)
    return out


def perm_order(p):
    import math
    seen = [False] * 27
    result = 1
    for i in range(27):
        if seen[i]:
            continue
        j, length = i, 0
        while not seen[j]:
            seen[j] = True
            length += 1
            j = p[j]
        result = math.lcm(result, length)
    return result


def transform_terms(g, terms):
    p, signs = g
    out = defaultdict(int)
    for mon, coeff in terms.items():
        factor = 1
        image = []
        for i in mon:
            factor *= signs[i]
            image.append(p[i])
        out[tuple(sorted(image))] += coeff * factor
    return {m: c for m, c in out.items() if c}


def simple_e6_permutations():
    weights, _, _ = e6_side()
    target_weights, _, target_graph = first_tits_side()
    source_weights, source_graph, _ = e6_side()
    iso = find_iso(source_graph, target_graph)
    inv = {v: k for k, v in iso.items()}

    # Reconstruct the E6 root subsystem in the same doubled E8 coordinates.
    from check_e6_minuscule_first_tits_basis_bridge import e8_roots, reflect
    roots = e8_roots()
    e6 = [r for r in roots if r[5:] in ((-1,) * 3, (0,) * 3, (1,) * 3)]
    functional = (1, 7, 49, 343, 2401, 16807, 117649, 823543)
    positive = [r for r in e6 if sum(r[i] * functional[i] for i in range(8)) > 0]
    positive_set = set(positive)
    simple = []
    for root in positive:
        if not any(tuple(root[i] - other[i] for i in range(8)) in positive_set for other in positive):
            simple.append(root)
    assert len(simple) == 6

    index = {w: i for i, w in enumerate(weights)}
    source_perms = [tuple(index[reflect(w, r)] for w in weights) for r in simple]
    transported = [tuple(iso[g[inv[t]]] for t in range(27)) for g in source_perms]
    return transported


def main():
    terms = cubic_terms()
    assert len(terms) == 45
    perms = simple_e6_permutations()
    lifts = []
    solution_nullities = []
    for p in perms:
        # Support is already the zero-weight triple relation.
        assert {tuple(sorted(p[i] for i in mon)) for mon in terms} == set(terms)
        signs, nullity = sign_lift(p, terms)
        g = (p, signs)
        assert transform_terms(g, terms) == terms
        lifts.append(g)
        solution_nullities.append(nullity)

    pair_orders = [[perm_order(tuple(perms[i][perms[j][k]] for k in range(27))) for j in range(6)] for i in range(6)]
    square_residuals = []
    for g in lifts:
        sq = signed_power(g, 2)
        assert sq[0] == tuple(range(27))
        assert transform_terms(sq, terms) == terms
        square_residuals.append(Counter(sq[1]))

    coxeter_residuals = []
    for i in range(6):
        for j in range(i + 1, 6):
            m = pair_orders[i][j]
            word = signed_power(signed_compose(lifts[i], lifts[j]), m)
            assert word[0] == tuple(range(27))
            assert transform_terms(word, terms) == terms
            coxeter_residuals.append((i, j, m, Counter(word[1])))

    strict_section = all(r == Counter({1: 27}) for r in square_residuals) and all(
        r[3] == Counter({1: 27}) for r in coxeter_residuals
    )
    assert not strict_section

    print('first_tits_cubic_monomials=45')
    print('simple_reflections=6')
    print('each_permutation_preserves_cubic_support=true')
    print('each_simple_reflection_has_signed_cubic_preserving_lift=true')
    print('sign_solution_affine_nullities=' + ','.join(map(str, solution_nullities)))
    print('strict_Weyl_section_from_selected_lifts=false')
    print('diagonal_cubic_preserving_2_torsion_residuals=true')
    print('interpretation=Tits/Weyl-normalizer extension; do not collapse to strict W(E6) linear section')
    for i, residual in enumerate(square_residuals):
        print(f'square_residual_{i}={dict(residual)}')
    for i, j, m, residual in coxeter_residuals:
        print(f'coxeter_residual_{i}_{j}_m{m}={dict(residual)}')


if __name__ == '__main__':
    main()
