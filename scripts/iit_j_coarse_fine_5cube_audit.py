#!/usr/bin/env python3
"""DASHI exact F3 5^3 coarse/fine operator audit, not IIT Phi or physical data.

The source law is iit_ternary_lattice_scaling.py's periodic three-axis sum.
F x(i,j,k) = x(i+1,j,k)+x(i,j+1,k)+x(i,j,k+1) mod 3.
J g(i,j,k) = g(i+j+k mod 5), with g on 5 cyclic coordinates.
P x(s) is the sum over all 25 sites satisfying i+j+k=s mod 5.
The certificate F^80=I-JP is exhaustively checked on 125 basis vectors.
"""
from __future__ import annotations

import argparse
from collections import Counter
from hashlib import sha256
from itertools import product
import json
from iit_ternary_lattice_scaling import rank_mod, torus_linear_matrix

Q, N, DIM = 3, 5, 3
COORDS = tuple(product(range(N), repeat=DIM))
INDEX = {c: i for i, c in enumerate(COORDS)}
SLICES = tuple(sum(c) % N for c in COORDS)
NEIGHBORS = tuple(
    tuple(INDEX[tuple((c[k] + int(k == axis)) % N for k in range(DIM))]
          for axis in range(DIM))
    for c in COORDS
)
SIZE = len(COORDS)


def step(state):
    return tuple(sum(state[j] for j in neighbors) % Q
                 for neighbors in NEIGHBORS)


def section(profile):
    return tuple(profile[s] % Q for s in SLICES)


def coarse(state):
    out = [0] * N
    for s, value in zip(SLICES, state):
        out[s] = (out[s] + value) % Q
    return tuple(out)


def basis(index, size=SIZE):
    return tuple(int(i == index) for i in range(size))


def fine(state):
    return tuple((a - b) % Q for a, b in
                 zip(state, section(coarse(state))))


def audit():
    assert set(Counter(SLICES).values()) == {N * N}
    # The '+one coordinate' interpretation is the GRAPH of a dependent
    # fourth address s=i+j+k mod 5. Exactly 125 admissible addresses,
    # not all 625 independent points of a four-axis size-five lattice.
    graph_addresses = tuple((*c, label) for c, label in zip(COORDS, SLICES))
    assert len(set(graph_addresses)) == SIZE
    assert all(sum(c[:3]) % N == c[3] for c in graph_addresses)
    for k in range(N):
        e = basis(k, N)
        assert coarse(section(e)) == e    # P J = 1 (25 = 1 mod 3)
        assert step(section(e)) == (0,) * SIZE  # F J = 0
    rank = rank_mod(torus_linear_matrix(N, DIM, Q, (0, 1, 2)), Q)
    assert rank == 120, rank
    # Context: "one 5-slot lost profile" is NOT a universal ternary-3D
    # rule. The source scan already shows different kernel multiplicity
    # when 3 divides the periodic side length (n=3).
    contrast_rank3 = rank_mod(torus_linear_matrix(3, 3, Q, (0, 1, 2)), Q)
    contrast_rank4 = rank_mod(torus_linear_matrix(4, 3, Q, (0, 1, 2)), Q)
    assert 27 - contrast_rank3 == 9
    assert 64 - contrast_rank4 == 4

    for k in range(SIZE):
        e = basis(k)
        assert coarse(step(e)) == (0,) * N  # P F = 0
        residual = fine(e)
        assert coarse(residual) == (0,) * N
        assert tuple((a + b) % Q for a, b in
                     zip(residual, section(coarse(e)))) == e
        state = e
        for _ in range(80):
            state = step(state)
        assert state == residual, ("F^80 != I-JP", k)
        assert step(state) == step(e)  # F^81 = F

    receipt = {
        "kind": "DASHI_F3_5CUBE_EXACT_LINEAR_ALGEBRA_NOT_IIT_PHI",
        "source": "scripts/iit_ternary_lattice_scaling.py",
        "field": "F3",
        "side": N, "spatial_dimension": DIM, "sites": SIZE,
        "rank": rank, "lost_kernel_dimensions": SIZE - rank,
        "retained_core_dimensions": rank,
        "diagonal_coarse_profile_dimensions": N,
        "diagonal_planes": N, "sites_per_plane": N * N,
        "plus_one_dependent_address_graph": {
            "ambient_four_axis_addresses": N ** 4,
            "valid_graph_addresses": len(graph_addresses),
            "auxiliary_label": "s=(i+j+k) mod 5",
            "fourth_coordinate_independent": False,
            "source_sites_unchanged": True,
        },
        "coarse_profiles": Q ** N,
        "source_states": str(Q ** SIZE),
        "retained_after_step": str(Q ** rank),
        "section_projection_identity": True,
        "transition_annihilates_section": True,
        "projection_annihilates_transition": True,
        "eighty_step_equals_identity_minus_section_projection": True,
        "transition_on_retained_core_period_divides_80": True,
        "lost_sector_equals_section_image": True,
        "retained_sector_equals_projection_kernel": True,
        "coarse_fine_exact_reopening": True,
        "tested_basis_vectors": SIZE,
        "not_an_extra_spatial_axis": True,
        "not_identified_with_j_harmonic_9_or_19683": True,
        "cross_size_falsifiers": {
            "ternary_3d_side_3_kernel": 27 - contrast_rank3,
            "ternary_3d_side_4_kernel": 64 - contrast_rank4,
            "ternary_3d_side_5_kernel": SIZE - rank,
            "universal_one_profile_kernel_claimed": False,
        },
        "no_agda_kernel_or_full_iit_receipt": True,
    }
    blob = json.dumps(receipt, sort_keys=True, separators=(",", ":")).encode()
    receipt["payload_sha256"] = sha256(blob).hexdigest()
    return receipt


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", default="")
    args = parser.parse_args()
    result = audit()
    print(json.dumps(result, indent=2, sort_keys=True))
    if args.json:
        with open(args.json, "w", encoding="utf-8") as f:
            json.dump(result, f, indent=2, sort_keys=True)
            f.write("\n")
