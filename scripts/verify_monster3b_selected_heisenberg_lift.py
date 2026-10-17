#!/usr/bin/env python3
"""Exact selected Monster-3B normalizer -> Heisenberg lift certificate.

Consumes the vendored ATLAS 2.Suz / 2.Suz:2 12-dimensional GF(3) matrices and
reuses the repository symplectic-normalization routines.  For the already
selected field-producing source word

    g2 g1 g2^-1 g1 g2^-1

it reconstructs the full 12x12 action in the repository X6 + X6* polarization.
The word has strict symplectic multiplier 1.  If C is the asymmetric Heisenberg
cocycle matrix, then

    D = M^T C M - C

is symmetric.  Hence over GF(3)

    q(x) = 2 x^T D x

has polarization D (since 1/2 = 2 mod 3), proving exactly

    q(x+y) + c(x,y)
      = q(x) + q(y) + c(Mx,My).

This is an algebraic matrix certificate, not exhaustive enumeration of all
3^24 ordered vector pairs.
"""
from __future__ import annotations

import json
from pathlib import Path

from analyze_monster3b_symplectic_compressions import (
    HALF,
    MOD,
    N,
    analyze_split_sources,
    inverse_mod,
    matmul,
    parse_meataxe_file,
    similitude_multiplier,
)

SELECTED_WORD = "g2 g1 g2^-1 g1 g2^-1"
EXPECTED_COMPRESSION = [
    [0, 2, 1, 0, 2, 1],
    [2, 0, 2, 1, 2, 2],
    [0, 0, 0, 0, 1, 2],
    [2, 0, 1, 2, 1, 2],
    [2, 0, 2, 2, 0, 2],
    [1, 0, 1, 0, 2, 2],
]


def transpose(a):
    return [list(row) for row in zip(*a)]


def sub_mod(a, b):
    return [[(x - y) % MOD for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def add_mod(a, b):
    return [[(x + y) % MOD for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def scalar_mod(k, a):
    return [[(k * x) % MOD for x in row] for row in a]


def rank_mod(a):
    a = [[x % MOD for x in row] for row in a]
    if not a:
        return 0
    rows, cols = len(a), len(a[0])
    r = 0
    for c in range(cols):
        pivot = next((i for i in range(r, rows) if a[i][c]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        inv = 1 if a[r][c] == 1 else 2
        a[r] = [(inv * x) % MOD for x in a[r]]
        for i in range(rows):
            if i != r and a[i][c]:
                q = a[i][c]
                a[i] = [(x - q * y) % MOD for x, y in zip(a[i], a[r])]
        r += 1
        if r == rows:
            break
    return r


def eye(n):
    return [[1 if i == j else 0 for j in range(n)] for i in range(n)]


def cocycle_matrix():
    c = [[0] * N for _ in range(N)]
    for i in range(HALF):
        c[HALF + i][i] = 1
    return c


def standard_symplectic_form():
    j = [[0] * N for _ in range(N)]
    for i in range(HALF):
        j[i][HALF + i] = 1
        j[HALF + i][i] = 2
    return j


def selected_word_matrix(generators):
    g1, g2 = generators
    g1_inv, g2_inv = inverse_mod(g1), inverse_mod(g2)
    letters = [g2, g1, g2_inv, g1, g2_inv]
    out = eye(N)
    for letter in letters:
        out = matmul(letter, out)
    return out


def build_receipt(root: Path):
    data = root / "data" / "atlas"
    inner = [
        parse_meataxe_file(data / "2SuzG1-f3r12B0.m1"),
        parse_meataxe_file(data / "2SuzG1-f3r12B0.m2"),
    ]
    outer = [
        parse_meataxe_file(data / "2Suzd2G1-f3r12aB0.m1"),
        parse_meataxe_file(data / "2Suzd2G1-f3r12aB0.m2"),
    ]

    analysis = analyze_split_sources(inner, outer, depth=0)
    # `analyze_split_sources` exposes the exact normalization basis and the
    # already-conjugated source generators through deterministic recomputation.
    from analyze_monster3b_symplectic_compressions import invariant_form, symplectic_basis

    form, _ = invariant_form(inner)
    basis, standard = symplectic_basis(form)
    basis_inv = inverse_mod(basis)
    standard_outer = [matmul(matmul(basis_inv, g), basis) for g in outer]

    m = selected_word_matrix(standard_outer)
    multiplier = similitude_multiplier(m, standard)
    compression = [row[:HALF] for row in m[:HALF]]

    c = cocycle_matrix()
    defect = sub_mod(matmul(matmul(transpose(m), c), m), c)
    defect_t = transpose(defect)
    symmetric = defect == defect_t

    # q(x)=2*x^T D x.  Its polarization is represented by
    # 2(D + D^T), which must equal D for the required coboundary identity.
    polarization = scalar_mod(2, add_mod(defect, defect_t))
    polarization_identity = polarization == defect

    # Matrix form of q(x+y)+c(x,y)=q(x)+q(y)+c(Mx,My).
    transported_minus_original = defect
    coboundary_identity = symmetric and polarization_identity and (
        transported_minus_original == defect
    )

    return {
        "schema": "dashi.monster3b.selected_heisenberg_lift.v1",
        "selected_word": SELECTED_WORD,
        "selected_word_matrix": m,
        "selected_word_symplectic_multiplier": multiplier,
        "compression_matrix": compression,
        "compression_matches_selected_receipt": compression == EXPECTED_COMPRESSION,
        "cocycle_matrix": c,
        "cocycle_defect_matrix": defect,
        "cocycle_defect_symmetric": symmetric,
        "cocycle_defect_rank": rank_mod(defect),
        "quadratic_polarization_identity": polarization_identity,
        "central_correction_formula": "q(x)=2*x^T*D*x over GF(3)",
        "heisenberg_coboundary_identity": coboundary_identity,
        "bruteforce_pair_enumeration_used": False,
        "authority_boundary": (
            "Exact finite matrix certificate for the selected source word. "
            "It does not identify the full 2.Suz:2 normalizer action with a "
            "physical Monster action or pay downstream orbit/stabilizer semantics."
        ),
    }


def main():
    root = Path(__file__).resolve().parents[1]
    receipt = build_receipt(root)
    assert receipt["selected_word_symplectic_multiplier"] == 1
    assert receipt["compression_matches_selected_receipt"]
    assert receipt["cocycle_defect_symmetric"]
    assert receipt["quadratic_polarization_identity"]
    assert receipt["heisenberg_coboundary_identity"]
    out = root / "outputs" / "monster3b_selected_heisenberg_lift_20261012.json"
    out.write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"selected_word={receipt['selected_word']}")
    print(f"symplectic_multiplier={receipt['selected_word_symplectic_multiplier']}")
    print(f"defect_rank={receipt['cocycle_defect_rank']}")
    print("cocycle_defect_symmetric=true")
    print("quadratic_polarization_identity=true")
    print("heisenberg_coboundary_identity=true")


if __name__ == "__main__":
    main()
