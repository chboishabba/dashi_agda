#!/usr/bin/env python3
"""Screen Monster-3B source words by X6 compression and Heisenberg lift data.

The inner 2.Suz pair fixes the alternating form.  The 2.Suz:2 extension may act
by symplectic similitudes, so after the common basis normalization we retain the
multiplier lambda for every source word.  Every word has an X6 compression
A_g=pi_X g iota_X.  For any nonzero similitude multiplier we also compute the
asymmetric-Heisenberg cocycle defect

    B(x,y) = c(gx,gy) - lambda c(x,y).

The alternating part cancels by similitude covariance, so B is symmetric.  In
characteristic three the quadratic correction

    q(x) = 2 B(x,x) = (1/2) B(x,x)

satisfies q(x+y)-q(x)-q(y)=B(x,y).  Hence

    (x,z) -> (g x, lambda z + q(x))

is the correct center-scaled Heisenberg lift candidate.  This is particularly
important for the preferred primitive field-selector word, whose multiplier is
2=-1 and therefore inverts/scales the center rather than fixing it.
"""
from __future__ import annotations

import argparse
import json
from collections import deque
from pathlib import Path

from analyze_monster3b_symplectic_field_candidates import (
    HALF, MOD, N, block, charpoly_info, eye, flatten, invariant_form,
    inverse_mod, is_zero, matmul, matvec, parse_dump, rank_mod,
    symplectic_basis,
)


def parse_meataxe_file(path):
    tokens = Path(path).read_text().split()
    if len(tokens) < 5:
        raise ValueError(f"invalid MeatAxe file: {path}")
    mode, field, rows, cols = map(int, tokens[:4])
    if mode != 1 or field != MOD or rows != N or cols != N:
        raise ValueError(
            f"expected MeatAxe 1 {MOD} {N} {N}, got {mode} {field} {rows} {cols}"
        )
    digits = "".join(tokens[4:])
    if len(digits) != rows * cols or any(ch not in "012" for ch in digits):
        raise ValueError(f"expected {rows * cols} GF(3) entries in {path}")
    return [[int(ch) for ch in digits[r * cols:(r + 1) * cols]]
            for r in range(rows)]


def scalar_matrix(matrix, scalar):
    return [[(scalar * x) % MOD for x in row] for row in matrix]


def transpose(matrix):
    return [list(row) for row in zip(*matrix)]


def matrix_sub(left, right):
    return [[(a - b) % MOD for a, b in zip(lrow, rrow)]
            for lrow, rrow in zip(left, right)]


def similitude_multiplier(matrix, standard_form):
    transported = matmul(matmul(transpose(matrix), standard_form), matrix)
    if transported == standard_form:
        return 1
    if transported == scalar_matrix(standard_form, 2):
        return 2
    return 0


def heisenberg_cocycle_matrix():
    matrix = [[0] * N for _ in range(N)]
    for i in range(HALF):
        matrix[HALF + i][i] = 1
    return matrix


def heisenberg_cocycle_defect(matrix, multiplier):
    cocycle = heisenberg_cocycle_matrix()
    transported = matmul(matmul(transpose(matrix), cocycle), matrix)
    return matrix_sub(transported, scalar_matrix(cocycle, multiplier))


def quadratic_correction_basis_data(defect):
    # q(x)=2*x^T B*x.  For symmetric B, diagonal coefficient is 2 B_ii
    # and the i<j cross coefficient simplifies to B_ij in F3.
    diagonal = [(2 * defect[i][i]) % MOD for i in range(N)]
    cross = [[i, j, defect[i][j]] for i in range(N)
             for j in range(i + 1, N) if defect[i][j] % MOD]
    return diagonal, cross


def cyclic_rank_e0(matrix):
    vector = [1] + [0] * (HALF - 1)
    columns = []
    for _ in range(HALF):
        columns.append(vector)
        vector = matvec(matrix, vector)
    rows = [[columns[c][r] for c in range(HALF)] for r in range(HALF)]
    return rank_mod(rows)


def swap01(vector):
    result = list(vector)
    result[0], result[1] = result[1], result[0]
    return result


def breaks_swap01_at_e0(matrix):
    e0 = [1] + [0] * (HALF - 1)
    return matvec(matrix, swap01(e0)) != swap01(matvec(matrix, e0))


def search_compressions(generators, standard_form, depth):
    letters = [(f"g{i+1}", matrix) for i, matrix in enumerate(generators)]
    letters += [(f"g{i+1}^-1", inverse_mod(matrix))
                for i, matrix in enumerate(generators)]

    identity = eye(N)
    queue = deque([(identity, [])])
    seen = {flatten(identity)}
    rows = []

    while queue:
        matrix, word = queue.popleft()
        if word:
            upper_left = block(matrix, 0, HALF, 0, HALF)
            lower_left = block(matrix, HALF, N, 0, HALF)
            charpoly, factor_degrees, irreducible = charpoly_info(upper_left)
            multiplier = similitude_multiplier(matrix, standard_form)
            defect = heisenberg_cocycle_defect(matrix, multiplier) if multiplier else None
            defect_symmetric = bool(defect is not None and defect == transpose(defect))
            correction_diagonal, correction_cross = (
                quadratic_correction_basis_data(defect)
                if defect_symmetric else ([], [])
            )
            rows.append({
                "word": " ".join(word),
                "length": len(word),
                "source_similitude_multiplier": multiplier,
                "stabilises_translation_lagrangian": is_zero(lower_left),
                "compression_matrix": upper_left,
                "compression_charpoly": charpoly,
                "compression_factor_degrees": factor_degrees,
                "compression_irreducible_degree6": irreducible,
                "cyclic_rank_e0": cyclic_rank_e0(upper_left),
                "breaks_swap01_at_e0": breaks_swap01_at_e0(upper_left),
                "heisenberg_cocycle_defect_symmetric": defect_symmetric,
                "heisenberg_cocycle_defect_matrix": defect,
                "heisenberg_center_correction_constructed": defect_symmetric,
                "heisenberg_center_correction_diagonal": correction_diagonal,
                "heisenberg_center_correction_cross_terms": correction_cross,
            })

        if len(word) >= depth:
            continue
        for name, generator in letters:
            nxt = matmul(generator, matrix)
            key = flatten(nxt)
            if key not in seen:
                seen.add(key)
                queue.append((nxt, word + [name]))

    return rows, len(seen)


def analyze_split_sources(inner_generators, outer_generators, depth):
    alternating_form, form_space_dimension = invariant_form(inner_generators)
    basis, standard_form = symplectic_basis(alternating_form)
    basis_inverse = inverse_mod(basis)

    standard_inner = [matmul(matmul(basis_inverse, g), basis)
                      for g in inner_generators]
    standard_outer = [matmul(matmul(basis_inverse, g), basis)
                      for g in outer_generators]

    inner_multipliers = [similitude_multiplier(m, standard_form)
                         for m in standard_inner]
    outer_multipliers = [similitude_multiplier(m, standard_form)
                         for m in standard_outer]

    rows, visited = search_compressions(standard_outer, standard_form, depth)
    irreducible = [row for row in rows if row["compression_irreducible_degree6"]]
    field_selector_hits = [row for row in irreducible
                           if row["cyclic_rank_e0"] == HALF
                           and row["breaks_swap01_at_e0"]]

    return {
        "field_order": MOD,
        "dimension": N,
        "inner_generator_count": len(inner_generators),
        "outer_generator_count": len(outer_generators),
        "invariant_alternating_form_space_dimension": form_space_dimension,
        "invariant_form": alternating_form,
        "symplectic_basis_columns": basis,
        "standard_form": standard_form,
        "inner_symplectic_multipliers": inner_multipliers,
        "outer_similitude_multipliers": outer_multipliers,
        "outer_generator_2_equals_inner_generator_2": (
            len(inner_generators) >= 2 and len(outer_generators) >= 2
            and outer_generators[1] == inner_generators[1]
        ),
        "search_depth": depth,
        "distinct_words_or_elements_visited": visited,
        "compression_rows": rows,
        "irreducible_degree6_compression_hits": irreducible,
        "k6_field_selector_numeric_hits": field_selector_hits,
        "requires_lagrangian_stabilizer_for_compression_field_test": False,
        "similitude_heisenberg_lift_rule": (
            "(x,z) -> (g x, lambda*z + q(x)); "
            "q(x)=2*(c(gx,gx)-lambda*c(x,x)) over GF(3)"
        ),
        "interpretation": (
            "Real ATLAS source words now yield both the X6 compression and the "
            "center-scaled Heisenberg correction data. Multiplier-2 outer words "
            "are retained as similitudes rather than falsely forced into strict Sp."
        ),
    }


def analyze(generators, depth):
    return analyze_split_sources(generators, generators, depth)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--matrix-dump")
    parser.add_argument("--inner-matrix", nargs=2)
    parser.add_argument("--outer-matrix", nargs=2)
    parser.add_argument("--search-depth", type=int, default=4)
    parser.add_argument("--output", default="monster3b_symplectic_compression_candidates.json")
    args = parser.parse_args()

    if args.inner_matrix or args.outer_matrix:
        if not (args.inner_matrix and args.outer_matrix):
            parser.error("--inner-matrix and --outer-matrix must be supplied together")
        result = analyze_split_sources(
            [parse_meataxe_file(path) for path in args.inner_matrix],
            [parse_meataxe_file(path) for path in args.outer_matrix],
            args.search_depth,
        )
    elif args.matrix_dump:
        result = analyze(parse_dump(args.matrix_dump), args.search_depth)
    else:
        parser.error("supply --matrix-dump or both --inner-matrix and --outer-matrix")

    Path(args.output).write_text(json.dumps(result, indent=2) + "\n")
    print("visited=", result["distinct_words_or_elements_visited"])
    print("compression_degree6_hits=", len(result["irreducible_degree6_compression_hits"]))
    print("k6_field_selector_numeric_hits=", len(result["k6_field_selector_numeric_hits"]))


if __name__ == "__main__":
    main()
