#!/usr/bin/env python3
"""Screen all short Monster-3B symplectic source words by X6 compression.

This complements `analyze_monster3b_symplectic_field_candidates.py`.
The older search only tested words stabilising the chosen translation
Lagrangian X6.  The downstream K6 selector needs only an F3-linear X6
endomorphism, so after the same-basis symplectic weld every source word has a
canonical compression

    A_g = pi_X g iota_X,

namely the upper-left 6x6 block in the repository X6 + X6* polarization.

This script therefore tests ALL visited short words for degree-six irreducible
characteristic polynomial, while retaining a flag for the stronger special case
where the word actually stabilises X6.

No source matrices are fabricated; the matrix dump must come from the existing
ATLAS acquisition helper.
"""
from __future__ import annotations

import argparse
import json
from collections import deque
from pathlib import Path

from analyze_monster3b_symplectic_field_candidates import (
    HALF,
    N,
    block,
    charpoly_info,
    eye,
    flatten,
    invariant_form,
    inverse_mod,
    is_zero,
    matmul,
    parse_dump,
    symplectic_basis,
)


def search_compressions(generators, depth):
    letters = [(f"g{i+1}", A) for i, A in enumerate(generators)]
    letters += [(f"g{i+1}^-1", inverse_mod(A)) for i, A in enumerate(generators)]

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
                    "compression_charpoly": charpoly,
                    "compression_factor_degrees": factor_degrees,
                    "compression_irreducible_degree6": irreducible,
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


def analyze(generators, depth):
    alternating_form, form_space_dimension = invariant_form(generators)
    basis, standard_form = symplectic_basis(alternating_form)
    basis_inverse = inverse_mod(basis)
    standard_generators = [
        matmul(matmul(basis_inverse, generator), basis)
        for generator in generators
    ]

    rows, visited = search_compressions(standard_generators, depth)
    irreducible = [row for row in rows if row["compression_irreducible_degree6"]]
    stabilising = [row for row in rows if row["stabilises_translation_lagrangian"]]
    stabilising_irreducible = [
        row
        for row in irreducible
        if row["stabilises_translation_lagrangian"]
    ]

    return {
        "field_order": 3,
        "dimension": 12,
        "generator_count": len(generators),
        "invariant_alternating_form_space_dimension": form_space_dimension,
        "invariant_form": alternating_form,
        "symplectic_basis_columns": basis,
        "standard_form": standard_form,
        "search_depth": depth,
        "distinct_words_or_elements_visited": visited,
        "compression_rows": rows,
        "irreducible_degree6_compression_hits": irreducible,
        "lagrangian_stabilizer_rows": stabilising,
        "lagrangian_stabilizer_irreducible_degree6_hits": stabilising_irreducible,
        "requires_lagrangian_stabilizer_for_compression_field_test": False,
        "interpretation": (
            "Every same-basis symplectic source word supplies an X6 compression. "
            "Lagrangian stabilisation is a stronger optional property, not a prerequisite "
            "for the downstream linear field-selector test."
        ),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--matrix-dump", required=True)
    parser.add_argument("--search-depth", type=int, default=4)
    parser.add_argument(
        "--output",
        default="monster3b_symplectic_compression_candidates.json",
    )
    args = parser.parse_args()

    result = analyze(parse_dump(args.matrix_dump), args.search_depth)
    Path(args.output).write_text(json.dumps(result, indent=2) + "\n")

    print("visited=", result["distinct_words_or_elements_visited"])
    print("compression_degree6_hits=", len(result["irreducible_degree6_compression_hits"]))
    print("lagrangian_stabilizer_hits=", len(result["lagrangian_stabilizer_rows"]))
    print(
        "stabilizer_degree6_hits=",
        len(result["lagrangian_stabilizer_irreducible_degree6_hits"]),
    )


if __name__ == "__main__":
    main()
