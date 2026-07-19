#!/usr/bin/env python3
"""Search physically local parametrix constants for the finite SU(2) Hessian.

Local Hessian inverses are glued with a symmetric diagonal partition of unity,
and A G*=I-R is tested in exponentially weighted row norms.  The search now
compares three genuinely finite-range patch geometries:

* isotropic rectangular cubes;
* unions of axis-oriented slabs;
* translated torus L1 balls of fixed radius.

The ball family is motivated by the actual coupling geometry of the gauge-fixed
Hessian.  On the 2^4 torus, radius-two balls contain 11 of 16 sites and radius-three
balls contain 15 of 16 sites, so both remain proper finite patches.  On larger
lattices the same fixed radii stay local rather than growing with total volume.

A finite candidate is accepted only when both left and right weighted norms are
strictly below one.  Spectral radius below one without the required weighted norm
is retained as an obstruction.  Closure is reported separately for every sampled
background, so finite searches never become a uniform small-field theorem by
aggregation.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any, Iterable, Sequence

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


def rectangular_patches(
    lat: PeriodicLattice,
    shape: Sequence[int],
) -> Iterable[tuple[tuple[int, ...], list[tuple[int, ...]]]]:
    shape = tuple(int(side) for side in shape)
    if len(shape) != lat.dim:
        raise ValueError(f"patch shape must have {lat.dim} entries")
    if any(side <= 0 or lat.L % side for side in shape):
        raise ValueError("every rectangular patch side must be a positive divisor of L")
    coarse_shape = tuple(lat.L // side for side in shape)
    for anchor_coarse in np.ndindex(*coarse_shape):
        anchor = tuple(shape[axis] * anchor_coarse[axis] for axis in range(lat.dim))
        sites = [
            tuple((anchor[axis] + offset[axis]) % lat.L for axis in range(lat.dim))
            for offset in np.ndindex(*shape)
        ]
        yield anchor, sites


def torus_ball_patches(
    lat: PeriodicLattice,
    radius: int,
) -> Iterable[tuple[tuple[int, ...], list[tuple[int, ...]]]]:
    if radius < 0:
        raise ValueError("ball radius must be nonnegative")
    all_sites = [tuple(site) for site in lat.sites()]
    for center in all_sites:
        sites = [site for site in all_sites if torus_l1(center, site, lat.L) <= radius]
        yield center, sites


def local_dofs(lat: PeriodicLattice, sites: list[tuple[int, ...]]) -> np.ndarray:
    indices: list[int] = []
    for site in sites:
        for mu in range(lat.dim):
            bond = lat.bond_index(site, mu)
            indices.extend((3 * bond, 3 * bond + 1, 3 * bond + 2))
    return np.asarray(indices, dtype=int)


def glued_site_patch_parametrix(
    H: np.ndarray,
    lat: PeriodicLattice,
    site_patches: Sequence[list[tuple[int, ...]]],
    metadata: dict[str, Any],
) -> tuple[np.ndarray, dict[str, Any]]:
    if not site_patches:
        raise ValueError("a patch family must contain at least one patch")

    dimension = H.shape[0]
    Gstar = np.zeros_like(H)
    coverage = np.zeros(dimension, dtype=float)
    local_minima: list[float] = []
    local_dimensions: list[int] = []
    local_site_counts: list[int] = []

    for sites in site_patches:
        indices = local_dofs(lat, sites)
        block = 0.5 * (H[np.ix_(indices, indices)] + H[np.ix_(indices, indices)].T)
        eigenvalues = np.linalg.eigvalsh(block)
        local_minima.append(float(eigenvalues[0]))
        local_dimensions.append(int(len(indices)))
        local_site_counts.append(len(sites))
        if eigenvalues[0] <= 1e-12:
            return Gstar, {
                "defined": False,
                "reason": "nonpositive local Hessian block",
                "local_lambda_min": float(eigenvalues[0]),
                **metadata,
            }
        inverse = np.linalg.inv(block)
        Gstar[np.ix_(indices, indices)] += inverse
        coverage[indices] += 1.0

    if np.any(coverage == 0):
        return Gstar, {
            "defined": False,
            "reason": "uncovered degree of freedom",
            **metadata,
        }

    # Symmetric partition of unity: W^{-1/2} (sum G_i) W^{-1/2}.
    weights = 1.0 / np.sqrt(coverage)
    Gstar = weights[:, None] * Gstar * weights[None, :]
    return Gstar, {
        "defined": True,
        "patch_count": len(site_patches),
        "local_lambda_min": min(local_minima),
        "local_dimension_max": max(local_dimensions),
        "local_site_count_min": min(local_site_counts),
        "local_site_count_max": max(local_site_counts),
        "proper_local": max(local_site_counts) < lat.n_sites,
        "coverage_min": float(np.min(coverage)),
        "coverage_max": float(np.max(coverage)),
        **metadata,
    }


def weighted_infinity_norm(
    matrix: np.ndarray,
    positions: list[tuple[int, ...]],
    L: int,
    mu: float,
) -> float:
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


def _candidate_key(candidate: dict[str, Any]) -> tuple[float, float, float, int]:
    worst = max(float(candidate["left"]), float(candidate["right"]))
    local_size = int(candidate.get("local_site_count_max", 10**9))
    return worst, float(candidate["mu"]), abs(1.0 - float(candidate["relaxation"])), local_size


def _family_specs(
    dim: int,
    local_sides: list[int],
    slab_thicknesses: list[int],
    ball_radii: list[int],
) -> list[dict[str, Any]]:
    families: list[dict[str, Any]] = []
    for side in local_sides:
        families.append({
            "patch_family": f"cube-{side}",
            "family_kind": "rectangles",
            "local_side": side,
            "shapes": [(side,) * dim],
        })
    for thickness in slab_thicknesses:
        shapes = [
            tuple(thickness if axis == orientation else 1 for axis in range(dim))
            for orientation in range(dim)
        ]
        families.append({
            "patch_family": f"axis-slabs-{thickness}",
            "family_kind": "rectangles",
            "slab_thickness": thickness,
            "shapes": shapes,
        })
    for radius in ball_radii:
        families.append({
            "patch_family": f"torus-ball-{radius}",
            "family_kind": "torus-ball",
            "ball_radius": radius,
        })
    return families


def _instantiate_family(
    lat: PeriodicLattice,
    family: dict[str, Any],
) -> tuple[list[list[tuple[int, ...]]], dict[str, Any]]:
    kind = family["family_kind"]
    metadata = {
        key: value
        for key, value in family.items()
        if key not in {"shapes", "family_kind"}
    }
    if kind == "rectangles":
        unique_shapes = list(dict.fromkeys(tuple(shape) for shape in family["shapes"]))
        patches = [
            sites
            for shape in unique_shapes
            for _, sites in rectangular_patches(lat, shape)
        ]
        metadata["patch_shapes"] = [list(shape) for shape in unique_shapes]
        return patches, metadata
    if kind == "torus-ball":
        patches = [sites for _, sites in torus_ball_patches(lat, int(family["ball_radius"]))]
        return patches, metadata
    raise ValueError(f"unknown patch family kind: {kind}")


def run_search(
    *,
    L: int,
    average_block: int,
    local_sides: list[int],
    mus: list[float],
    radii: list[float],
    seeds: int,
    relaxations: list[float] | None = None,
    slab_thicknesses: list[int] | None = None,
    ball_radii: list[int] | None = None,
) -> dict[str, Any]:
    if relaxations is None:
        relaxations = [1.0]
    if slab_thicknesses is None:
        slab_thicknesses = []
    if ball_radii is None:
        ball_radii = []
    if not relaxations or any(value <= 0.0 for value in relaxations):
        raise ValueError("relaxations must be a nonempty list of positive values")

    lat = PeriodicLattice(L)
    positions = dof_positions(lat)
    families = _family_specs(lat.dim, local_sides, slab_thicknesses, ball_radii)
    trials: list[dict[str, Any]] = []

    for radius in radii:
        for seed in range(seeds):
            background = identity_links(lat) if radius == 0 else random_background(lat, radius, seed)
            _, Q = block_average_matrix(lat, average_block, background)
            H = gauge_fixed_hessian(lat, background=background, average=Q)
            for family in families:
                patches, metadata = _instantiate_family(lat, family)
                Gstar, local = glued_site_patch_parametrix(H, lat, patches, metadata)
                trial: dict[str, Any] = {
                    "radius": radius,
                    "seed": seed,
                    **local,
                }
                if local.get("defined"):
                    trial["relaxation_trials"] = []
                    for relaxation in relaxations:
                        relaxed = relaxation * Gstar
                        right_residual = np.eye(H.shape[0]) - H @ relaxed
                        left_residual = np.eye(H.shape[0]) - relaxed @ H
                        spectral_radius_right = float(np.max(np.abs(np.linalg.eigvals(right_residual))))
                        spectral_radius_left = float(np.max(np.abs(np.linalg.eigvals(left_residual))))
                        weighted_norms = [
                            {
                                "mu": mu,
                                "right": weighted_infinity_norm(right_residual, positions, L, mu),
                                "left": weighted_infinity_norm(left_residual, positions, L, mu),
                            }
                            for mu in mus
                        ]
                        strict_weighted = [
                            item for item in weighted_norms
                            if item["right"] < 1.0 and item["left"] < 1.0
                        ]
                        trial["relaxation_trials"].append({
                            "relaxation": relaxation,
                            "spectral_radius_right": spectral_radius_right,
                            "spectral_radius_left": spectral_radius_left,
                            "spectrally_contractive": (
                                spectral_radius_right < 1.0 and spectral_radius_left < 1.0
                            ),
                            "weighted_norms": weighted_norms,
                            "convergent_candidates": strict_weighted,
                            "weighted_norm_obstruction": (
                                spectral_radius_right < 1.0
                                and spectral_radius_left < 1.0
                                and not strict_weighted
                            ),
                        })
                trials.append(trial)

    convergent: list[dict[str, Any]] = []
    spectral_obstructions: list[dict[str, Any]] = []
    all_weighted_candidates: list[dict[str, Any]] = []
    metadata_keys = (
        "patch_family",
        "patch_shapes",
        "local_side",
        "slab_thickness",
        "ball_radius",
        "local_site_count_min",
        "local_site_count_max",
    )
    for trial in trials:
        for relaxed in trial.get("relaxation_trials", []):
            base = {
                "radius": trial["radius"],
                "seed": trial["seed"],
                "proper_local": trial["proper_local"],
                "relaxation": relaxed["relaxation"],
            }
            for key in metadata_keys:
                if key in trial:
                    base[key] = trial[key]
            if relaxed["weighted_norm_obstruction"]:
                spectral_obstructions.append({
                    **base,
                    "spectral_radius_right": relaxed["spectral_radius_right"],
                    "spectral_radius_left": relaxed["spectral_radius_left"],
                    "best_weighted_norm": min(
                        max(item["left"], item["right"])
                        for item in relaxed["weighted_norms"]
                    ),
                })
            for item in relaxed["weighted_norms"]:
                candidate = {**base, **item}
                all_weighted_candidates.append(candidate)
                if item["right"] < 1.0 and item["left"] < 1.0:
                    convergent.append(candidate)

    proper_convergent = [item for item in convergent if item["proper_local"]]
    proper_weighted = [item for item in all_weighted_candidates if item["proper_local"]]
    best_proper = min(proper_weighted, key=_candidate_key) if proper_weighted else None

    background_closure = []
    for radius in radii:
        for seed in range(seeds):
            candidates = [
                item for item in proper_convergent
                if item["radius"] == radius and item["seed"] == seed
            ]
            background_closure.append({
                "radius": radius,
                "seed": seed,
                "strict_proper_local_bound": bool(candidates),
                "best_candidate": min(candidates, key=_candidate_key) if candidates else None,
            })

    return {
        "claim_scope": "finite_lattice_only",
        "lattice_extent": L,
        "average_block": average_block,
        "trials": trials,
        "convergent_candidates": convergent,
        "proper_local_convergent_candidates": proper_convergent,
        "spectral_without_weighted_norm_obstructions": spectral_obstructions,
        "best_proper_local_candidate": best_proper,
        "background_closure": background_closure,
        "has_strict_weighted_remainder_bound": bool(convergent),
        "has_strict_proper_local_weighted_remainder_bound": bool(proper_convergent),
        "all_sampled_backgrounds_have_strict_proper_local_bound": (
            bool(background_closure)
            and all(item["strict_proper_local_bound"] for item in background_closure)
        ),
        "global_inverse_only": bool(convergent) and not bool(proper_convergent),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--L", type=int, default=2)
    parser.add_argument("--average-block", type=int, default=2)
    parser.add_argument("--local-sides", default="1,2")
    parser.add_argument("--slab-thicknesses", default="2")
    parser.add_argument("--ball-radii", default="2,3")
    parser.add_argument("--mus", default="0,0.05,0.1")
    parser.add_argument("--radii", default="0,0.01,0.03")
    parser.add_argument("--relaxations", default="0.25,0.5,0.75,1")
    parser.add_argument("--seeds", type=int, default=1)
    parser.add_argument("--out", default="operator_analysis/local-parametrix-search.json")
    args = parser.parse_args()
    report = run_search(
        L=args.L,
        average_block=args.average_block,
        local_sides=[int(value) for value in args.local_sides.split(",") if value],
        slab_thicknesses=[int(value) for value in args.slab_thicknesses.split(",") if value],
        ball_radii=[int(value) for value in args.ball_radii.split(",") if value],
        mus=[float(value) for value in args.mus.split(",") if value],
        radii=[float(value) for value in args.radii.split(",") if value],
        seeds=args.seeds,
        relaxations=[float(value) for value in args.relaxations.split(",") if value],
    )
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    write_receipt(args.out, {"operator": "local_parametrix_search", **report})
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
