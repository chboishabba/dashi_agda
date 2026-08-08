#!/usr/bin/env python3
"""Exhaustively validate the finite-Heisenberg model used by the 3B lane.

This is not a substitute for an actual MN3B matrix representation.  It proves
that the explicit F_3^6 Schrödinger/Weyl carrier used by the dashboard has the
claimed symplectic, character-degree, and generator commutation properties.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

P = 3
N = 6
H = P**N
ZETA = np.exp(2j * np.pi / P)


def vectors() -> np.ndarray:
    values = np.arange(H, dtype=np.int64)
    return np.stack([(values // (P**j)) % P for j in range(N)], axis=1)


def symplectic_matrix() -> np.ndarray:
    matrix = np.zeros((N, N), dtype=np.int64)
    matrix[:3, 3:] = np.eye(3, dtype=np.int64)
    matrix[3:, :3] = -np.eye(3, dtype=np.int64)
    return matrix % P


def rank_mod_p(matrix: np.ndarray, p: int) -> int:
    work = matrix.copy() % p
    rows, cols = work.shape
    rank = 0
    for col in range(cols):
        pivot = next((r for r in range(rank, rows) if work[r, col] % p), None)
        if pivot is None:
            continue
        work[[rank, pivot]] = work[[pivot, rank]]
        inverse = pow(int(work[rank, col]), -1, p)
        work[rank] = (work[rank] * inverse) % p
        for row in range(rows):
            if row != rank and work[row, col] % p:
                work[row] = (work[row] - work[row, col] * work[rank]) % p
        rank += 1
    return rank


def pairing(xs: np.ndarray, ys: np.ndarray, form: np.ndarray) -> np.ndarray:
    return np.einsum("...i,ij,...j->...", xs, form, ys) % P


def validate() -> dict[str, int | bool]:
    xs = vectors()
    form = symplectic_matrix()
    basis = np.eye(N, dtype=np.int64)

    if H != 729 or xs.shape != (729, 6):
        raise AssertionError("unexpected F_3^6 carrier")
    if rank_mod_p(form, P) != N:
        raise AssertionError("symplectic form is degenerate")
    if not np.all(pairing(xs, xs, form) == 0):
        raise AssertionError("symplectic form is not alternating")

    # Exhaustive generator-level bilinearity.  Since the six basis vectors
    # generate F_3^6, these checks certify the implemented linear formula.
    for e in basis:
        lhs_left = pairing((xs + e) % P, basis[:, None, :], form)
        rhs_left = (
            pairing(xs[None, :, :], basis[:, None, :], form)
            + pairing(
                np.broadcast_to(e, xs.shape)[None, :, :],
                basis[:, None, :],
                form,
            )
        ) % P
        if not np.array_equal(lhs_left, rhs_left):
            raise AssertionError("left bilinearity failed")

    # Weyl relation for all 36 standard translation/modulation generator
    # pairs and all 729 basis states.  We use
    #
    #   T_a e_x = e_{x+a},
    #   M_b e_x = zeta^{<b,x>} e_x,
    #
    # hence M_b T_a = zeta^{<b,a>} T_a M_b.
    generator_checks = 0
    for a in basis:
        shifted = (xs + a) % P
        for b in basis:
            repeated_b = np.broadcast_to(b, xs.shape)
            left_phase = ZETA ** pairing(repeated_b, shifted, form)
            right_phase = (
                ZETA ** int(pairing(b, a, form))
                * ZETA ** pairing(repeated_b, xs, form)
            )
            if not np.allclose(left_phase, right_phase, atol=1e-12, rtol=0):
                raise AssertionError("Weyl commutation relation failed")
            generator_checks += H

    linear_character_count = P ** (2 * 3)
    nonlinear_character_count = P - 1
    nonlinear_character_degree = P**3
    extraspecial_order = P ** (1 + 2 * 3)
    degree_sum_squares = (
        linear_character_count
        + nonlinear_character_count * nonlinear_character_degree**2
    )
    if degree_sum_squares != extraspecial_order:
        raise AssertionError("extraspecial character-degree sum of squares failed")

    # The Monster case uses n=6 rather than n=3.  Check its exact scale
    # separately without allocating 3^12 states.
    monster_heisenberg_degree = 3**6
    monster_linear_count = 3**12
    monster_extraspecial_order = 3**13
    monster_degree_sum_squares = (
        monster_linear_count + 2 * monster_heisenberg_degree**2
    )
    if monster_degree_sum_squares != monster_extraspecial_order:
        raise AssertionError("3^(1+12) character-degree sum of squares failed")
    if monster_heisenberg_degree * (12 + 78) != 65610:
        raise AssertionError("729*(12+78) != 65610")
    if 10 * 3**8 != 90 * 3**6:
        raise AssertionError("10*3^8 and 90*3^6 charts disagree")

    # Leech/weight-two coordinate identity explaining the integer 196608.
    if 196560 + 24 + 24 != 196608:
        raise AssertionError("Leech coordinate subtotal failed")
    if 2 * 276 != 24 * 23:
        raise AssertionError("off-diagonal pair count failed")
    if 196608 + 276 != 196884:
        raise AssertionError("Leech weight-two completion failed")
    if 196608 + 275 != 196883:
        raise AssertionError("Monster nontrivial degree completion failed")

    return {
        "field_prime": P,
        "schrodinger_coordinate_dimension": N,
        "schrodinger_state_count": H,
        "symplectic_rank": rank_mod_p(form, P),
        "alternating_state_checks": H,
        "weyl_generator_state_checks": generator_checks,
        "monster_heisenberg_degree": monster_heisenberg_degree,
        "monster_extraspecial_order": monster_extraspecial_order,
        "monster_degree_sum_squares": monster_degree_sum_squares,
        "monster_multiplicity_degree": 90,
        "monster_nontrivial_phase_degree": 65610,
        "leech_coordinate_subtotal": 196608,
        "leech_off_diagonal_pairs": 276,
        "all_checks_passed": True,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("build/monster_3b_heisenberg_model_certificate.json"),
    )
    args = parser.parse_args()
    payload = validate()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
