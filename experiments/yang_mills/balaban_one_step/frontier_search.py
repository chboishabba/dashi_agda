#!/usr/bin/env python3
"""Search for proof constants in the finite SU(2) one-step problem.

Every result is indexed by the finite lattice/background used.  A failed
inequality is retained as a counterexample candidate rather than promoted.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import numpy as np

from common import (
    PeriodicLattice,
    block_average_matrix,
    gauge_fixed_hessian,
    identity_links,
    lie_field_to_links,
    write_receipt,
)


def canonical_section(Q: np.ndarray, *, rtol: float = 1e-12) -> tuple[np.ndarray, float]:
    """Construct S=Q^T(QQ^T)^-1 and return ||QS-I||_2."""
    middle = Q @ Q.T
    smallest = float(np.linalg.eigvalsh(0.5 * (middle + middle.T))[0])
    if smallest <= rtol:
        raise np.linalg.LinAlgError(
            f"averaging constraints are dependent: lambda_min(QQ*)={smallest:.3e}"
        )
    section = Q.T @ np.linalg.inv(middle)
    residual = float(np.linalg.norm(Q @ section - np.eye(Q.shape[0]), ord=2))
    return section, residual


def corrected_background_section(
    Q0: np.ndarray, QB: np.ndarray, S0: np.ndarray, *, rtol: float = 1e-12
) -> dict[str, Any]:
    """Implement S_B=S_0(I+(Q_B-Q_0)S_0)^-1 exactly at matrix level."""
    perturbation = QB - Q0
    ES0 = perturbation @ S0
    radius = float(np.linalg.norm(ES0, ord=2))
    middle = np.eye(Q0.shape[0]) + ES0
    singular = np.linalg.svd(middle, compute_uv=False)
    smallest = float(singular[-1])
    result: dict[str, Any] = {
        "perturbation_section_norm": radius,
        "neumann_sufficient": bool(radius < 1.0),
        "middle_smallest_singular_value": smallest,
    }
    if smallest <= rtol:
        result["corrected_section_exists"] = False
        return result
    SB = S0 @ np.linalg.inv(middle)
    result.update(
        corrected_section_exists=True,
        corrected_section_norm=float(np.linalg.norm(SB, ord=2)),
        corrected_section_residual=float(
            np.linalg.norm(QB @ SB - np.eye(QB.shape[0]), ord=2)
        ),
        neumann_norm_bound=(
            float(np.linalg.norm(S0, ord=2) / (1.0 - radius))
            if radius < 1.0
            else None
        ),
    )
    return result


def hodge_poincare_diagnostic(H: np.ndarray) -> dict[str, Any]:
    symmetric = 0.5 * (H + H.T)
    eigenvalues = np.linalg.eigvalsh(symmetric)
    smallest = float(eigenvalues[0])
    return {
        "smallest_eigenvalue": smallest,
        "largest_eigenvalue": float(eigenvalues[-1]),
        "candidate_hodge_constant": float(1.0 / smallest) if smallest > 0 else None,
        "coercive_on_full_finite_space": bool(smallest > 0),
    }


def diagonal_parametrix_diagnostic(H: np.ndarray) -> dict[str, Any]:
    """Test the first local/Jacobi parametrix A G*=I-R."""
    diagonal = np.diag(H)
    if np.any(np.abs(diagonal) < 1e-14):
        return {"defined": False, "reason": "zero diagonal pivot"}
    Gstar = np.diag(1.0 / diagonal)
    residual = np.eye(H.shape[0]) - H @ Gstar
    rho = float(np.linalg.norm(residual, ord=2))
    spectral_radius = float(np.max(np.abs(np.linalg.eigvals(residual))))
    return {
        "defined": True,
        "weighted_remainder_norm_mu0": rho,
        "spectral_radius": spectral_radius,
        "convergent_candidate": bool(rho < 1.0),
    }


def random_background(lat: PeriodicLattice, radius: float, seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    field = rng.normal(size=lat.shape + (lat.dim, 3))
    norms = np.linalg.norm(field, axis=-1, keepdims=True)
    field = field / np.maximum(norms, 1e-30)
    amplitudes = rng.uniform(0.0, radius, size=norms.shape)
    return lie_field_to_links(field * amplitudes)


def run_search(
    *, L: int, block: int, radii: list[float], seeds: int
) -> dict[str, Any]:
    lat = PeriodicLattice(L)
    _, Q0 = block_average_matrix(lat, block, identity_links(lat))
    S0, section_residual = canonical_section(Q0)
    H0 = gauge_fixed_hessian(lat, background=identity_links(lat), average=Q0)

    backgrounds: list[dict[str, Any]] = []
    for radius in radii:
        for seed in range(seeds):
            background = random_background(lat, radius, seed)
            _, QB = block_average_matrix(lat, block, background)
            HB = gauge_fixed_hessian(lat, background=background, average=QB)
            section = corrected_background_section(Q0, QB, S0)
            eig = np.linalg.eigvalsh(0.5 * (HB + HB.T))
            backgrounds.append(
                {
                    "radius": radius,
                    "seed": seed,
                    **section,
                    "background_smallest_eigenvalue": float(eig[0]),
                    "coercivity_loss": float(
                        np.linalg.eigvalsh(0.5 * (H0 + H0.T))[0] - eig[0]
                    ),
                }
            )

    return {
        "claim_scope": "finite_lattice_only",
        "lattice_extent": L,
        "block_length": block,
        "fine_dimension": int(Q0.shape[1]),
        "coarse_dimension": int(Q0.shape[0]),
        "zero_background_section": {
            "right_inverse_residual": section_residual,
            "section_norm": float(np.linalg.norm(S0, ord=2)),
            "constraints_independent": bool(section_residual < 1e-10),
        },
        "zero_background_hodge": hodge_poincare_diagnostic(H0),
        "diagonal_parametrix": diagonal_parametrix_diagnostic(H0),
        "background_trials": backgrounds,
        "all_background_sections_closed": bool(
            all(
                trial.get("corrected_section_residual", np.inf) < 1e-9
                for trial in backgrounds
            )
        ),
        "worst_background_section_radius": float(
            max((trial["perturbation_section_norm"] for trial in backgrounds), default=0.0)
        ),
        "worst_background_coercivity": float(
            min((trial["background_smallest_eigenvalue"] for trial in backgrounds), default=np.inf)
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--L", type=int, default=2)
    parser.add_argument("--block", type=int, default=2)
    parser.add_argument("--radii", default="0,0.01,0.03,0.05")
    parser.add_argument("--seeds", type=int, default=2)
    parser.add_argument(
        "--out", default="operator_analysis/frontier_search.json"
    )
    args = parser.parse_args()
    radii = [float(value) for value in args.radii.split(",") if value.strip()]
    result = run_search(L=args.L, block=args.block, radii=radii, seeds=args.seeds)
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    write_receipt(args.out, {"operator": "su2_frontier_constant_search", **result})
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
