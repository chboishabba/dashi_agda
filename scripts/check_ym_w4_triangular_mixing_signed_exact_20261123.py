#!/usr/bin/env python3
"""Exact sign-bearing W4 triangular-mixing representation check.

Finite representation-level shadow of the 2602.0096 Thm 8.5 / Cor 8.6
preventive lock; not a kernel receipt or a proof of the full source theorem.
"""
from itertools import combinations, permutations
import sympy as S


def w4_elements():
    for perm in permutations(range(4)):
        for bits in range(16):
            signs = tuple(-1 if (bits >> i) & 1 else 1 for i in range(4))
            yield perm, signs


def generators():
    swap = ((1, 0, 2, 3), (1, 1, 1, 1))
    cycle = ((1, 2, 3, 0), (1, 1, 1, 1))
    sign0 = ((0, 1, 2, 3), (-1, 1, 1, 1))
    return swap, cycle, sign0


def r4_matrix(perm, signs):
    m = S.zeros(4)
    for col in range(4):
        m[perm[col], col] = signs[col]
    return m


def wedge_matrix(perm, signs, pairs, index):
    m = S.zeros(len(pairs))
    for col, (mu, nu) in enumerate(pairs):
        row_mu, row_nu = perm[mu], perm[nu]
        sign = signs[mu] * signs[nu]
        if row_mu > row_nu:
            row_mu, row_nu = row_nu, row_mu
            sign = -sign
        m[index[(row_mu, row_nu)], col] = sign
    return m


def symmetric_variables(n):
    vars_ = S.symbols(f"m0:{n * (n + 1) // 2}")
    positions = list(combinations(range(n), 2))
    positions = [(a, a) for a in range(n)] + positions
    m = S.zeros(n)
    for var, (a, b) in zip(vars_, positions):
        m[a, b] = var
        m[b, a] = var
    return vars_, positions, m


def constraint_rows(matrices, m, vars_):
    eqs = []
    n = m.rows
    for w in matrices:
        diff = w.T * m * w - m
        eqs.extend(diff[a, b] for a in range(n) for b in range(a, n))
    a, _ = S.linear_eq_to_matrix(eqs, vars_)
    return a


def canonical_vector(vec, positions, n):
    scaled = vec * S.lcm([x.q for x in vec])
    entries = list(scaled)
    for i, (a, b) in enumerate(positions):
        if a == b:
            entries[i] = entries[i] / entries[0]
    pivot = next(x for x in entries if x != 0)
    if pivot < 0:
        entries = [-x for x in entries]
    out = S.zeros(len(entries), 1)
    for i, x in enumerate(entries):
        out[i] = S.simplify(x)
    return out


def main():
    pairs = list(combinations(range(4), 2))
    index = {pair: i for i, pair in enumerate(pairs)}
    gens = [r4_matrix(*g) for g in generators()]
    wedge_gens = [wedge_matrix(*g, pairs, index) for g in generators()]

    r4vars, r4pos, r4m = symmetric_variables(4)
    r4null = constraint_rows(gens, r4m, r4vars).nullspace()
    assert len(r4null) == 1, f"dim4 W4-invariant operator space = {len(r4null)}"
    r4basis = canonical_vector(r4null[0], r4pos, 4)
    r4form = S.zeros(4)
    for x, (a, b) in zip(r4basis, r4pos):
        r4form[a, b] = x
        r4form[b, a] = x
    assert r4form == S.eye(4), f"dim4 invariant basis is not scalar: {r4form}"

    wvars, wpos, wm = symmetric_variables(6)
    a = constraint_rows(wedge_gens, wm, wvars)
    null = a.nullspace()
    assert len(null) == 1, f"Lambda^2 invariant form space = {len(null)}"
    basis = canonical_vector(null[0], wpos, 6)
    form = S.zeros(6)
    for x, (p, q) in zip(basis, wpos):
        form[p, q] = x
        form[q, p] = x
    assert form == S.eye(6), f"Lambda^2 invariant basis is not scalar: {form}"

    trace_expr = sum(wvars[i] for i, pos in enumerate(wpos) if pos[0] == pos[1])
    trace_row, _ = S.linear_eq_to_matrix([trace_expr], wvars)
    aniso_null = a.col_join(trace_row).nullspace()
    assert not aniso_null, f"trace-free anisotropic invariants survive: {aniso_null}"

    count = 0
    for perm, signs in w4_elements():
        p = r4_matrix(perm, signs)
        w = wedge_matrix(perm, signs, pairs, index)
        assert p.T * r4form * p == r4form
        assert w.T * form * w == form
        count += 1
    assert count == 384, f"|W4| = {count}"

    sign0 = wedge_matrix(*generators()[2], pairs, index)
    sign_profile = tuple(sign0[i, i] for i in range(6))
    assert sign_profile == (-1, -1, -1, 1, 1, 1), sign_profile

    print(
        "PASS exact sign-bearing W4 lock: |W4|=384, "
        "Lambda^2 invariant forms=1 (identity), trace-free anisotropic invariants=0, "
        "dim4 W4-invariant operators=1 (scalar=O(4)-invariant), "
        "full-group conjugations=384/384, sign-flip profile=" + str(sign_profile)
    )


if __name__ == "__main__":
    main()
