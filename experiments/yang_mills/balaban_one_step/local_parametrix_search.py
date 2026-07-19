#!/usr/bin/env python3
"""Search physically local parametrix constants for the finite SU(2) Hessian.

For each localization side M, invert the Hessian restricted to bonds whose
origins lie in each M^4 cube, glue the local inverses with the exact diagonal
partition-of-unity coverage, and evaluate A G*=I-R in exponentially weighted
kernel norms.  A result with ||R||_mu<1 is a finite convergence certificate
candidate for the random-walk proof lane; failure is retained as a counterexample
to that localization choice.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any, Iterable

import numpy as np

from common import (
    PeriodicLattice,
    block_average_matrix,
    gauge_fixed_hessian,
    identity_links,
    lie_field_to_links,
    write_receipt,
)


def torus_l1(left: tuple[int, ...], right: tuple[int, ...], L: int) -> int:
    total = 0
    for a, b in zip(left, right):
        delta = abs(a - b)
        total += min(delta, L - delta)
    return total


def dof_positions(lat: PeriodicLattice) -> list[tuple[int, ...]]:
    positions: list[tuple[int, ...]] = [()] * (3 * lat.n_bonds)
    for site in lat.sites():
        for mu in range(lat.dim):
            bond = lat.bond_index(site, mu)
            for color in range(3):
                positions[3 * bond + color] = tuple(site)
    return positions


def cubes(lat: PeriodicLattice, side: int) -> Iterable[tuple[tuple[int, ...], list[tuple[int, ...]]]]:
    if side <= 0 or lat.L % side:
        raise ValueError("local side must be a positive divisor of L")
    coarse = lat.L // side
    for anchor_coarse in np.ndindex(*(coarse,) * lat.dim):
        anchor = tuple(side * coordinate for coordinate in anchor_coarse)
        sites = []
        for offset in np.ndindex(*(side,) * lat.dim):
            sites.append(tuple((anchor[axis] + offset[axis]) % lat.L for axis in range(lat.dim)))
        yield anchor, sites


def local_dofs(lat: PeriodicLattice, sites: list[tuple[int, ...]]) -> np.ndarray:
    indices: list[int] = []
    for site in sites:
        for mu in range(lat.dim):
            bond = lat.bond_index(site, mu)
            indices.extend((3 * bond, 3 * bond + 1, 3 * bond + 2))
    return np.asarray(indices, dtype=int)


def glued_local_parametrix(H: np.ndarray, lat: PeriodicLattice, side: int) -> tuple[np.ndarray, dict[str, Any]]:
    dimension = H.shape[0]
    Gstar = np.zeros_like(H)
    coverage = np.zeros(dimension, dtype=float)
    local_minima: list[float] = []
    local_dimensions: list[int] = []
    for _, sites in cubes(lat, side):
        indices = local_dofs(lat, sites)
        block = 0.5 * (H[np.ix_(indices, indices)] + H[np.ix_(indices, indices)].T)
        eigenvalues = np.linalg.eigvalsh(block)
        local_minima.append(float(eigenvalues[0]))
        local_dimensions.append(int(len(indices)))
        if eigenvalues[0] <= 1e-12:
            return Gstar, {
                "defined": False,
                "reason": "nonpositive local Hessian block",
                "local_lambda_min": float(eigenvalues[0]),
            }
        inverse = np.linalg.inv(block)
        Gstar[np.ix_(indices, indices)] += inverse
        coverage[indices] += 1.0
    if np.any(coverage == 0):
        return Gstar, {"defined": False, "reason": "uncovered degree of freedom"}
    # Symmetric partition of unity: W^{-1/2} (sum G_i) W^{-1/2}.
    weights = 1.0 / np.sqrt(coverage)
    Gstar = weights[:, None] * Gstar * weights[None, :]
    return Gstar, {
        "defined": True,
        "local_lambda_min": min(local_minima),
        "local_dimension_max": max(local_dimensions),
        "coverage_min": float(np.min(coverage)),
        "coverage_max": float(np.max(coverage)),
    }


def weighted_infinity_norm(matrix: np.ndarray, positions: list[tuple[int, ...]], L: int, mu: float) -> float:
    weighted_rows = []
    for i, left in enumerate(positions):
        row = 0.0
        for j, right in enumerate(positions):
            row += math.exp(mu * torus_l1(left, right, L)) * abs(float(matrix[i, j]))
        weighted_rows.append(row)
    return float(max(weighted_rows, default=0.0))


def random_background(lat: PeriodicLattice, radius: float, seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    field = rng.normal(size=lat.shape + (lat.dim, 3))
    field /= np.maximum(np.linalg.norm(field, axis=-1, keepdims=True), 1e-30)
    field *= rng.uniform(0.0, radius, size=field.shape[:-1] + (1,))
    return lie_field_to_links(field)


def run_search(
    *, L: int, average_block: int, local_sides: list[int], mus: list[float], radii: list[float], seeds: int
) -> dict[str, Any]:
    lat = PeriodicLattice(L)
    positions = dof_positions(lat)
    trials: list[dict[str, Any]] = []
    for radius in radii:
        for seed in range(seeds):
            background = identity_links(lat) if radius == 0 else random_background(lat, radius, seed)
            _, Q = block_average_matrix(lat, average_block, background)
            H = gauge_fixed_hessian(lat, background=background, average=Q)
            for side in local_sides:
                Gstar, local = glued_local_parametrix(H, lat, side)
                trial: dict[str, Any] = {"radius": radius, "seed": seed, "local_side": side, **local}
                if local.get("defined"):
                    right_residual = np.eye(H.shape[0]) - H @ Gstar
                    left_residual = np.eye(H.shape[0]) - Gstar @ H
                    trial["spectral_radius_right"] = float(
                        np.max(np.abs(np.linalg.eigvals(right_residual)))
                    )
                    trial["spectral_radius_left"] = float(
                        np.max(np.abs(np.linalg.eigvals(left_residual)))
                    )
                    trial["weighted_norms"] = [
                        {
                            "mu": mu,
                            "right": weighted_infinity_norm(right_residual, positions, L, mu),
                            "left": weighted_infinity_norm(left_residual, positions, L, mu),
                        }
                        for mu in mus
                    ]
                    trial["convergent_candidates"] = [
                        item for item in trial["weighted_norms"]
                        if item["right"] < 1.0 and item["left"] < 1.0
                    ]
                trials.append(trial)
    convergent = [
        {"radius": t["radius"], "seed": t["seed"], "local_side": t["local_side"], **entry}
        for t in trials for entry in t.get("convergent_candidates", [])
    ]
    return {
        "claim_scope": "finite_lattice_only",
        "lattice_extent": L,
        "average_block": average_block,
        "trials": trials,
        "convergent_candidates": convergent,
        "has_strict_weighted_remainder_bound": bool(convergent),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--L", type=int, default=2)
    parser.add_argument("--average-block", type=int, default=2)
    parser.add_argument("--local-sides", default="1,2")
    parser.add_argument("--mus", default="0,0.05,0.1")
    parser.add_argument("--radii", default="0,0.01,0.03")
    parser.add_argument("--seeds", type=int, default=1)
    parser.add_argument("--out", default="operator_analysis/local-parametrix-search.json")
    args = parser.parse_args()
    report = run_search(
        L=args.L,
        average_block=args.average_block,
        local_sides=[int(value) for value in args.local_sides.split(",") if value],
        mus=[float(value) for value in args.mus.split(",") if value],
        radii=[float(value) for value in args.radii.split(",") if value],
        seeds=args.seeds,
    )
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    write_receipt(args.out, {"operator": "local_parametrix_search", **report})
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
