#!/usr/bin/env python3
"""Exhaustively validate the finite-Heisenberg model used by the 3B lane.

The Schrodinger coordinate is X=F_3^6, with dual X*.  The extraspecial
quotient is V=X+X*=F_3^12 with its standard alternating form.  The Weyl model
uses the perfect evaluation pairing X* x X -> F_3.

This proves the explicit model identities but does not substitute for a
concrete MN3B matrix representation.
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


def full_symplectic_matrix() -> np.ndarray:
    matrix = np.zeros((2 * N, 2 * N), dtype=np.int64)
    matrix[:N, N:] = np.eye(N, dtype=np.int64)
    matrix[N:, :N] = -np.eye(N, dtype=np.int64)
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


def evaluation(duals: np.ndarray, states: np.ndarray) -> np.ndarray:
    return np.sum(duals * states, axis=-1) % P


def validate() -> dict[str, int | bool]:
    xs = vectors()
    basis = np.eye(N, dtype=np.int64)
    duality = np.eye(N, dtype=np.int64)
    full_form = full_symplectic_matrix()

    if H != 729 or xs.shape != (729, 6):
        raise AssertionError("unexpected X=F_3^6 carrier")
    if rank_mod_p(duality, P) != N:
        raise AssertionError("X-X* evaluation pairing is degenerate")
    if rank_mod_p(full_form, P) != 2 * N:
        raise AssertionError("full symplectic quotient form is degenerate")
    if not np.array_equal((full_form + full_form.T) % P, np.zeros_like(full_form)):
        raise AssertionError("full quotient form is not alternating")
    if np.any(np.diag(full_form) % P):
        raise AssertionError("full quotient form has nonzero diagonal")

    # Bilinearity of the perfect X*-X pairing for every state and standard
    # basis generator on each side.
    bilinear_checks = 0
    for a in basis:
        shifted = (xs + a) % P
        for b in basis:
            repeated_b = np.broadcast_to(b, xs.shape)
            lhs = evaluation(repeated_b, shifted)
            rhs = (
                evaluation(repeated_b, xs)
                + int(evaluation(b, a))
            ) % P
            if not np.array_equal(lhs, rhs):
                raise AssertionError("evaluation pairing bilinearity failed")
            bilinear_checks += H

    # T_a e_x=e_(x+a), M_b e_x=zeta^<b,x>e_x, hence
    # M_b T_a=zeta^<b,a>T_a M_b.
    weyl_checks = 0
    for a in basis:
        shifted = (xs + a) % P
        for b in basis:
            repeated_b = np.broadcast_to(b, xs.shape)
            left_phase = ZETA ** evaluation(repeated_b, shifted)
            right_phase = (
                ZETA ** int(evaluation(b, a))
                * ZETA ** evaluation(repeated_b, xs)
            )
            if not np.allclose(left_phase, right_phase, atol=1e-12, rtol=0):
                raise AssertionError("Weyl commutation relation failed")
            weyl_checks += H

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

    # A two-plane U in the translation Lagrangian has order nine.  C[X]
    # restricts to 3^(6-2)=81 copies of Reg(U).
    if 3**2 != 9 or 3 ** (6 - 2) != 81 or 9 * 81 != H:
        raise AssertionError("Lagrangian two-plane restriction identity failed")

    full_two_planes = 5883904390
    full_isotropic_two_planes = 1961279320
    full_nonisotropic_two_planes = 3922625070
    if 16 * full_two_planes != (3**12 - 1) * (3**11 - 1):
        raise AssertionError("full Gaussian two-plane count failed")
    if 16 * full_isotropic_two_planes != (3**12 - 1) * (3**10 - 1):
        raise AssertionError("full isotropic two-plane count failed")
    if full_isotropic_two_planes + full_nonisotropic_two_planes != full_two_planes:
        raise AssertionError("full symplectic two-plane partition failed")

    # Leech weight-two coordinate subtotal and correctly placed conformal line.
    if 196560 + 24 + 24 != 196608:
        raise AssertionError("Leech coordinate subtotal failed")
    if 2 * 276 != 24 * 23:
        raise AssertionError("off-diagonal pair count failed")
    if 196608 + 276 != 196884:
        raise AssertionError("Leech weight-two completion failed")
    if 196560 + 24 + 23 + 276 != 196883:
        raise AssertionError("conformal-line quotient failed")

    return {
        "field_prime": P,
        "lagrangian_dimension": N,
        "schrodinger_state_count": H,
        "perfect_pairing_rank": rank_mod_p(duality, P),
        "full_symplectic_dimension": 2 * N,
        "full_symplectic_rank": rank_mod_p(full_form, P),
        "pairing_bilinearity_state_checks": bilinear_checks,
        "weyl_generator_state_checks": weyl_checks,
        "monster_heisenberg_degree": monster_heisenberg_degree,
        "monster_extraspecial_order": monster_extraspecial_order,
        "monster_degree_sum_squares": monster_degree_sum_squares,
        "monster_multiplicity_degree": 90,
        "monster_nontrivial_phase_degree": 65610,
        "translation_two_plane_order": 9,
        "regular_restriction_multiplicity": 81,
        "full_symplectic_two_plane_count": full_two_planes,
        "full_isotropic_two_plane_count": full_isotropic_two_planes,
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
