#!/usr/bin/env python3
"""Finite audit for the Leray-restricted rank-one triadic symbol.

This is a numerical algebra harness, not a Navier-Stokes proof certificate.
It audits the finite-dimensional classification used by the triadic
zero-mode boundary surfaces:

    M_c = P_c (b tensor a) P_c : T_c S^2 -> T_c S^2,

where c = normalize(rho * a + b), P_c is the Leray/tangent projector at the
output direction, and (b tensor a) v = b (a . v).

In tangent coordinates this is exactly a rank-one 2x2 map

    M = (P_c b) (P_c a)^T.

The classification being stress-tested is:

  * image family: if P_c b is nonzero, then P_c b is an eigenvector;
  * kernel family: if P_c a is nonzero, every tangent vector perpendicular to
    P_c a is a zero eigenvector.

Degenerate cases are expected and are reported separately.  Promotion remains
false: this script checks the single-depth finite algebra only, not cascade
closure, Lei-Ren-Tian transfer, or PDE leakage sign.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

import numpy as np


EPS = 1.0e-12


@dataclass(frozen=True)
class AuditRow:
    index: int
    rho: float
    c_norm_before_normalize: float
    image_norm: float
    covector_norm: float
    image_eigenvalue: float
    determinant: float
    trace: float
    rank_one_second_singular_value: float
    image_direction_residual: float | None
    kernel_direction_residual: float | None
    numpy_min_eigen_residual: float
    numpy_max_eigen_residual: float
    tangent_leakage_residual: float
    trace_eigenvalue_error: float
    determinant_zero_error: float
    degenerate_reason: str | None


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=20000)
    parser.add_argument("--seed", type=int, default=20260608)
    parser.add_argument("--rho-min", type=float, default=0.25)
    parser.add_argument("--rho-max", type=float, default=4.0)
    parser.add_argument(
        "--near-resonance-threshold",
        type=float,
        default=1.0e-8,
        help="Reject triads with |rho*a+b| below this threshold.",
    )
    parser.add_argument(
        "--degenerate-threshold",
        type=float,
        default=1.0e-8,
        help="Treat |P_c a| or |P_c b| below this threshold as degenerate.",
    )
    parser.add_argument(
        "--classification-tolerance",
        type=float,
        default=1.0e-9,
        help="Residual tolerance for pass/fail counters.",
    )
    parser.add_argument(
        "--json-output",
        type=Path,
        default=None,
        help="Optional path to write the JSON summary.",
    )
    parser.add_argument(
        "--show-worst",
        type=int,
        default=5,
        help="Include this many worst nondegenerate rows in the JSON summary.",
    )
    parser.add_argument(
        "--skip-degenerate-probes",
        action="store_true",
        help="Do not include deterministic degenerate-case probes in the summary.",
    )
    return parser.parse_args()


def unit(v: np.ndarray) -> np.ndarray:
    n = float(np.linalg.norm(v))
    if n <= EPS:
        raise ValueError("cannot normalize near-zero vector")
    return v / n


def random_unit(rng: np.random.Generator) -> np.ndarray:
    return unit(rng.normal(size=3))


def tangent_project(c: np.ndarray, v: np.ndarray) -> np.ndarray:
    return v - float(np.dot(c, v)) * c


def tangent_basis(c: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    candidates = (
        np.array([1.0, 0.0, 0.0]),
        np.array([0.0, 1.0, 0.0]),
        np.array([0.0, 0.0, 1.0]),
    )
    seed = min(candidates, key=lambda e: abs(float(np.dot(c, e))))
    e1 = unit(tangent_project(c, seed))
    e2 = unit(np.cross(c, e1))
    return e1, e2


def matrix_in_basis(u: np.ndarray, v: np.ndarray, basis: tuple[np.ndarray, np.ndarray]) -> np.ndarray:
    """Return coordinates of rank-one tangent map x -> u (v . x)."""

    e1, e2 = basis
    u2 = np.array([float(np.dot(e1, u)), float(np.dot(e2, u))])
    v2 = np.array([float(np.dot(e1, v)), float(np.dot(e2, v))])
    return np.outer(u2, v2)


def residual_for_eigenvector(matrix: np.ndarray, vector: np.ndarray, eigenvalue: float) -> float:
    return float(np.linalg.norm(matrix @ vector - eigenvalue * vector))


def eig_residuals(matrix: np.ndarray) -> tuple[float, float]:
    values, vectors = np.linalg.eig(matrix)
    residuals: list[float] = []
    for col, value in enumerate(values):
        vector = np.real(vectors[:, col])
        vnorm = float(np.linalg.norm(vector))
        if vnorm <= EPS:
            residuals.append(float("inf"))
            continue
        vector = vector / vnorm
        residuals.append(float(np.linalg.norm(matrix @ vector - float(np.real(value)) * vector)))
    residuals.sort()
    return residuals[0], residuals[-1]


def row_degenerate_reason(
    c_norm: float,
    image_norm: float,
    covector_norm: float,
    threshold: float,
) -> str | None:
    reasons: list[str] = []
    if c_norm <= threshold:
        reasons.append("near_resonant_output")
    if image_norm <= threshold:
        reasons.append("image_direction_Pcb_near_zero")
    if covector_norm <= threshold:
        reasons.append("covector_direction_Pca_near_zero")
    return ",".join(reasons) if reasons else None


def row_from_vectors(
    rng: np.random.Generator,
    index: int,
    a: np.ndarray,
    b: np.ndarray,
    rho: float,
    degenerate_threshold: float,
) -> AuditRow:
    raw_c = rho * a + b
    c_norm = float(np.linalg.norm(raw_c))
    c = raw_c / c_norm
    basis = tangent_basis(c)
    pca = tangent_project(c, a)
    pcb = tangent_project(c, b)
    image_norm = float(np.linalg.norm(pcb))
    covector_norm = float(np.linalg.norm(pca))
    matrix = matrix_in_basis(pcb, pca, basis)

    singular_values = np.linalg.svd(matrix, compute_uv=False)
    second_singular = float(singular_values[1]) if len(singular_values) > 1 else 0.0
    trace = float(np.trace(matrix))
    determinant = float(np.linalg.det(matrix))
    image_eigenvalue = float(np.dot(pca, pcb))

    image_residual: float | None = None
    kernel_residual: float | None = None

    if image_norm > degenerate_threshold:
        e1, e2 = basis
        image_coords = np.array([float(np.dot(e1, pcb)), float(np.dot(e2, pcb))])
        image_coords = image_coords / float(np.linalg.norm(image_coords))
        image_residual = residual_for_eigenvector(matrix, image_coords, image_eigenvalue)

    if covector_norm > degenerate_threshold:
        e1, e2 = basis
        covector_coords = np.array([float(np.dot(e1, pca)), float(np.dot(e2, pca))])
        kernel_coords = np.array([-covector_coords[1], covector_coords[0]])
        kernel_coords = kernel_coords / float(np.linalg.norm(kernel_coords))
        kernel_residual = residual_for_eigenvector(matrix, kernel_coords, 0.0)

    min_eig_residual, max_eig_residual = eig_residuals(matrix)

    # Reconstruct the ambient output from tangent coordinates and check that it
    # remains tangent after the Leray restriction.
    probe = unit(rng.normal(size=2))
    e1, e2 = basis
    tangent_probe = probe[0] * e1 + probe[1] * e2
    ambient_output = tangent_project(c, pcb * float(np.dot(pca, tangent_probe)))
    tangent_leakage_residual = abs(float(np.dot(c, ambient_output)))

    return AuditRow(
        index=index,
        rho=rho,
        c_norm_before_normalize=c_norm,
        image_norm=image_norm,
        covector_norm=covector_norm,
        image_eigenvalue=image_eigenvalue,
        determinant=determinant,
        trace=trace,
        rank_one_second_singular_value=second_singular,
        image_direction_residual=image_residual,
        kernel_direction_residual=kernel_residual,
        numpy_min_eigen_residual=min_eig_residual,
        numpy_max_eigen_residual=max_eig_residual,
        tangent_leakage_residual=tangent_leakage_residual,
        trace_eigenvalue_error=abs(trace - image_eigenvalue),
        determinant_zero_error=abs(determinant),
        degenerate_reason=row_degenerate_reason(c_norm, image_norm, covector_norm, degenerate_threshold),
    )


def make_row(
    rng: np.random.Generator,
    index: int,
    rho_min: float,
    rho_max: float,
    resonance_threshold: float,
    degenerate_threshold: float,
) -> AuditRow:
    for _ in range(10_000):
        a = random_unit(rng)
        b = random_unit(rng)
        rho = float(rng.uniform(rho_min, rho_max))
        raw_c = rho * a + b
        c_norm = float(np.linalg.norm(raw_c))
        if c_norm > resonance_threshold:
            return row_from_vectors(rng, index, a, b, rho, degenerate_threshold)
    raise RuntimeError("failed to sample nonresonant triad")


def deterministic_degenerate_probes(
    rng: np.random.Generator, threshold: float
) -> list[dict[str, Any]]:
    e1 = np.array([1.0, 0.0, 0.0])
    e2 = np.array([0.0, 1.0, 0.0])
    e3 = np.array([0.0, 0.0, 1.0])
    inv_sqrt2 = 1.0 / math.sqrt(2.0)
    probes = [
        ("both_projectors_zero_a_equals_b", e1, e1, 1.0),
        ("covector_zero_a_parallel_c", e1, e2, 1.0e6),
        ("image_zero_b_parallel_c", e1, e2, 1.0e-6),
        ("near_resonant_opposite_inputs", e1, -e1 + 1.0e-9 * e2, 1.0),
        ("nondegenerate_control_orthogonal_inputs", e1, e2, 1.0),
        (
            "nondegenerate_control_oblique_inputs",
            unit(e1 + e2),
            unit(inv_sqrt2 * e1 + 0.5 * e2 + 0.5 * e3),
            0.75,
        ),
    ]
    rows: list[dict[str, Any]] = []
    for index, (name, a, b, rho) in enumerate(probes):
        c_norm = float(np.linalg.norm(rho * a + b))
        if c_norm <= EPS:
            rows.append(
                {
                    "name": name,
                    "rho": rho,
                    "c_norm_before_normalize": c_norm,
                    "degenerate_reason": "exact_resonant_output_unconstructible",
                }
            )
            continue
        row = row_from_vectors(rng, -1 - index, unit(a), unit(b), rho, threshold)
        payload = asdict(row)
        payload["name"] = name
        rows.append(payload)
    return rows


def finite_percentiles(values: list[float], percentiles: tuple[float, ...]) -> dict[str, float | None]:
    if not values:
        return {f"p{int(p)}": None for p in percentiles}
    arr = np.array(values, dtype=float)
    return {f"p{int(p)}": float(np.percentile(arr, p)) for p in percentiles}


def distribution(values: list[float]) -> dict[str, float | None]:
    if not values:
        return {
            "count": 0,
            "min": None,
            "mean": None,
            "median": None,
            "p95": None,
            "p99": None,
            "max": None,
        }
    arr = np.array(values, dtype=float)
    return {
        "count": int(arr.size),
        "min": float(np.min(arr)),
        "mean": float(np.mean(arr)),
        "median": float(np.median(arr)),
        "p95": float(np.percentile(arr, 95)),
        "p99": float(np.percentile(arr, 99)),
        "max": float(np.max(arr)),
    }


def summarize(
    rows: list[AuditRow],
    args: argparse.Namespace,
    degenerate_probes: list[dict[str, Any]],
) -> dict[str, Any]:
    nondegenerate = [row for row in rows if row.degenerate_reason is None]
    degenerate = [row for row in rows if row.degenerate_reason is not None]

    image_residuals = [
        row.image_direction_residual
        for row in rows
        if row.image_direction_residual is not None
    ]
    kernel_residuals = [
        row.kernel_direction_residual
        for row in rows
        if row.kernel_direction_residual is not None
    ]
    combined_nonnull = [
        max(
            row.image_direction_residual or 0.0,
            row.kernel_direction_residual or 0.0,
            row.trace_eigenvalue_error,
            row.determinant_zero_error,
            row.rank_one_second_singular_value,
            row.tangent_leakage_residual,
        )
        for row in nondegenerate
    ]
    tol = float(args.classification_tolerance)
    degenerate_reasons: dict[str, int] = {}
    for row in degenerate:
        reason = row.degenerate_reason or "unknown"
        degenerate_reasons[reason] = degenerate_reasons.get(reason, 0) + 1

    worst_rows = sorted(
        nondegenerate,
        key=lambda row: max(
            row.image_direction_residual or 0.0,
            row.kernel_direction_residual or 0.0,
            row.trace_eigenvalue_error,
            row.determinant_zero_error,
            row.rank_one_second_singular_value,
        ),
        reverse=True,
    )[: max(0, int(args.show_worst))]

    return {
        "contract": "ns_leray_rank_one_symbol_audit",
        "scope": "finite_rank_one_leray_symbol_algebra_only_not_pde_or_clay_proof",
        "promotion": False,
        "seed": int(args.seed),
        "samples_requested": int(args.samples),
        "samples_completed": len(rows),
        "rho_range": [float(args.rho_min), float(args.rho_max)],
        "near_resonance_threshold": float(args.near_resonance_threshold),
        "degenerate_threshold": float(args.degenerate_threshold),
        "classification_tolerance": tol,
        "nondegenerate_count": len(nondegenerate),
        "degenerate_count": len(degenerate),
        "degenerate_reasons": degenerate_reasons,
        "image_direction_statement": "P_c b is an eigenvector of P_c(b tensor a)P_c with eigenvalue <P_c a,P_c b> when P_c b is nonzero",
        "kernel_direction_statement": "any tangent vector perpendicular to P_c a is a zero eigenvector when P_c a is nonzero",
        "residual_distributions": {
            "image_direction": distribution([float(x) for x in image_residuals]),
            "kernel_direction": distribution([float(x) for x in kernel_residuals]),
            "numpy_min_eigen_residual": distribution([row.numpy_min_eigen_residual for row in rows]),
            "numpy_max_eigen_residual": distribution([row.numpy_max_eigen_residual for row in rows]),
            "rank_one_second_singular_value": distribution([row.rank_one_second_singular_value for row in rows]),
            "trace_minus_image_eigenvalue_abs": distribution([row.trace_eigenvalue_error for row in rows]),
            "determinant_abs": distribution([row.determinant_zero_error for row in rows]),
            "tangent_leakage_abs": distribution([row.tangent_leakage_residual for row in rows]),
            "combined_nonnull_nonnegative_checks": distribution(combined_nonnull),
        },
        "pass_counts": {
            "image_direction_residual_le_tolerance": sum(x <= tol for x in image_residuals),
            "kernel_direction_residual_le_tolerance": sum(x <= tol for x in kernel_residuals),
            "trace_identity_le_tolerance": sum(row.trace_eigenvalue_error <= tol for row in rows),
            "determinant_zero_le_tolerance": sum(row.determinant_zero_error <= tol for row in rows),
            "rank_one_second_singular_le_tolerance": sum(row.rank_one_second_singular_value <= tol for row in rows),
            "tangent_output_leakage_le_tolerance": sum(row.tangent_leakage_residual <= tol for row in rows),
            "nondegenerate_rows_all_classification_checks_le_tolerance": sum(x <= tol for x in combined_nonnull),
        },
        "worst_nondegenerate_rows": [asdict(row) for row in worst_rows],
        "deterministic_degenerate_probes": degenerate_probes,
        "notes": [
            "This verifies the single-depth rank-one linear algebra only.",
            "Degenerate rows correspond to P_c a or P_c b nearly vanishing and are classified separately.",
            "Cascade-closed output width and compensated leakage PDE sign remain independent proof obligations.",
        ],
    }


def main() -> int:
    args = parse_args()
    if args.samples < 0:
        raise ValueError("--samples must be nonnegative")
    if args.rho_min <= 0.0 or args.rho_max <= 0.0 or args.rho_min > args.rho_max:
        raise ValueError("--rho-min and --rho-max must be positive with min <= max")

    rng = np.random.default_rng(args.seed)
    rows = [
        make_row(
            rng=rng,
            index=index,
            rho_min=float(args.rho_min),
            rho_max=float(args.rho_max),
            resonance_threshold=float(args.near_resonance_threshold),
            degenerate_threshold=float(args.degenerate_threshold),
        )
        for index in range(int(args.samples))
    ]
    probe_rng = np.random.default_rng(args.seed + 1)
    degenerate_probes = (
        []
        if args.skip_degenerate_probes
        else deterministic_degenerate_probes(probe_rng, float(args.degenerate_threshold))
    )
    summary = summarize(rows, args, degenerate_probes)
    text = json.dumps(summary, indent=2, sort_keys=True)
    print(text)

    if args.json_output is not None:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(text + "\n", encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
