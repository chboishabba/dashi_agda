#!/usr/bin/env python3
"""Screen Monster-3B source words by X6 compression.

The 2.Suz socle representation fixes the alternating form.  The 2.Suz:2
extension contains an outer generator with symplectic multiplier -1 (=2 mod 3),
so the outer generating pair must NOT be passed to the old strict
``invariant_form`` solver.  Instead we:

  1. solve the unique invariant alternating form from the inner 2.Suz pair;
  2. normalize that form to the repository X6 + X6* standard polarization;
  3. conjugate the 2.Suz:2 generators through the same basis change;
  4. record their symplectic-similitude multipliers;
  5. screen every short outer word through the canonical compression

         A_g = pi_X g iota_X,

     i.e. its upper-left 6x6 block.

The downstream K6 selector only needs a same-carrier F3-linear endomorphism,
so Lagrangian stabilization is retained as a stronger optional property rather
than a prerequisite.
"""
from __future__ import annotations

import argparse
import json
from collections import deque
from pathlib import Path

from analyze_monster3b_symplectic_field_candidates import (
    HALF,
    MOD,
    N,
    block,
    charpoly_info,
    eye,
    flatten,
    invariant_form,
    inverse_mod,
    is_zero,
    matmul,
    matvec,
    parse_dump,
    rank_mod,
    symplectic_basis,
)


def parse_meataxe_file(path):
    """Parse the small integer MeatAxe matrices used by the ATLAS files."""
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
    return [
        [int(ch) for ch in digits[r * cols : (r + 1) * cols]]
        for r in range(rows)
    ]


def scalar_matrix(matrix, scalar):
    return [[(scalar * x) % MOD for x in row] for row in matrix]


def transpose(matrix):
    return [list(row) for row in zip(*matrix)]


def similitude_multiplier(matrix, standard_form):
    transported = matmul(matmul(transpose(matrix), standard_form), matrix)
    if transported == standard_form:
        return 1
    if transported == scalar_matrix(standard_form, 2):
        return 2
    return 0


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


def search_compressions(generators, depth):
    letters = [(f"g{i+1}", matrix) for i, matrix in enumerate(generators)]
    letters += [
        (f"g{i+1}^-1", inverse_mod(matrix))
        for i, matrix in enumerate(generators)
    ]

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
            rows.append(
                {
                    "word": " ".join(word),
                    "length": len(word),
                    "stabilises_translation_lagrangian": is_zero(lower_left),
                    "compression_matrix": upper_left,
                    "compression_charpoly": charpoly,
                    "compression_factor_degrees": factor_degrees,
                    "compression_irreducible_degree6": irreducible,
                    "cyclic_rank_e0": cyclic_rank_e0(upper_left),
                    "breaks_swap01_at_e0": breaks_swap01_at_e0(upper_left),
                }
            )

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
    """Use inner 2.Suz to fix the form; screen the 2.Suz:2 extension."""
    alternating_form, form_space_dimension = invariant_form(inner_generators)
    basis, standard_form = symplectic_basis(alternating_form)
    basis_inverse = inverse_mod(basis)

    standard_inner = [
        matmul(matmul(basis_inverse, generator), basis)
        for generator in inner_generators
    ]
    standard_outer = [
        matmul(matmul(basis_inverse, generator), basis)
        for generator in outer_generators
    ]

    inner_multipliers = [
        similitude_multiplier(matrix, standard_form) for matrix in standard_inner
    ]
    outer_multipliers = [
        similitude_multiplier(matrix, standard_form) for matrix in standard_outer
    ]

    rows, visited = search_compressions(standard_outer, depth)
    irreducible = [row for row in rows if row["compression_irreducible_degree6"]]
    field_selector_hits = [
        row
        for row in irreducible
        if row["cyclic_rank_e0"] == HALF and row["breaks_swap01_at_e0"]
    ]

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
            len(inner_generators) >= 2
            and len(outer_generators) >= 2
            and outer_generators[1] == inner_generators[1]
        ),
        "search_depth": depth,
        "distinct_words_or_elements_visited": visited,
        "compression_rows": rows,
        "irreducible_degree6_compression_hits": irreducible,
        "k6_field_selector_numeric_hits": field_selector_hits,
        "requires_lagrangian_stabilizer_for_compression_field_test": False,
        "interpretation": (
            "The inner 2.Suz pair fixes the unique alternating form. The outer "
            "2.Suz:2 generator may be anti-symplectic/similitude with multiplier 2; "
            "after the same basis weld, every source word still gives an F3-linear "
            "X6 compression. Degree-six/cyclic/swap-breaking hits pay the numerical "
            "K6 selector conditions but not the final chosen-GF(729) action intertwiner."
        ),
    }


def analyze(generators, depth):
    """Legacy strict-symplectic path retained for existing callers."""
    return analyze_split_sources(generators, generators, depth)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--matrix-dump")
    parser.add_argument("--inner-matrix", nargs=2)
    parser.add_argument("--outer-matrix", nargs=2)
    parser.add_argument("--search-depth", type=int, default=4)
    parser.add_argument(
        "--output",
        default="monster3b_symplectic_compression_candidates.json",
    )
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
    print(
        "compression_degree6_hits=",
        len(result["irreducible_degree6_compression_hits"]),
    )
    print(
        "k6_field_selector_numeric_hits=",
        len(result["k6_field_selector_numeric_hits"]),
    )


if __name__ == "__main__":
    main()
