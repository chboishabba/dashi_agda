#!/usr/bin/env python3
"""Candidate-only Fourier triad-edge depletion audit.

This is the first diagnostic keyed to the physical edge-transfer lane, rather
than to physical-space strain telemetry.  It samples exact integer zero-sum
triads from a Fourier snapshot, computes the three modal energy transfers,
and tests a *stated candidate* helical-mismatch defect against transfer-edge
variation and weighted bad-edge mass.  It cannot prove the local hierarchy or
bad-edge sparsity theorem; a failed ratio is useful falsification evidence.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np


SCRIPT_NAME = "scripts/ns_triad_edge_depletion_audit.py"
DEFAULT_ARCHIVE = Path(
    "/home/c/Documents/code/dashiCFD/outputs/"
    "sprint65_pressure_reconstruction_N128_seed0_gpu/"
    "ns3d_N128_seed0_gpu_pressure.npz"
)
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_edge_depletion_audit_N128_20260716.json"
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_ARCHIVE)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--frame", type=int, default=0)
    parser.add_argument("--cutoff", type=int, default=8)
    parser.add_argument("--max-triads", type=int, default=12000)
    parser.add_argument("--thresholds", type=float, nargs="*", default=(0.1, 0.25, 0.5, 0.75))
    return parser.parse_args()


def authority() -> dict[str, bool]:
    return {
        "candidate_only": True,
        "empirical_non_promoting": True,
        "theorem_authority": False,
        "clay_authority": False,
        "promoted": False,
    }


def load_velocity(path: Path, frame: int) -> np.ndarray:
    with np.load(path, allow_pickle=False) as data:
        velocity = np.asarray(data["velocity_snapshots"], dtype=np.float64)
    if velocity.ndim != 5:
        raise ValueError(f"unsupported velocity_snapshots shape {velocity.shape!r}")
    if velocity.shape[1] == 3:
        return velocity[frame]
    if velocity.shape[-1] == 3:
        return np.moveaxis(velocity[frame], -1, 0)
    raise ValueError(f"cannot locate velocity component axis in {velocity.shape!r}")


def projector(k: np.ndarray, value: np.ndarray) -> np.ndarray:
    return value - k * np.dot(k, value) / np.dot(k, k)


def index(k: tuple[int, int, int], n: int) -> tuple[int, int, int]:
    return tuple(component % n for component in k)


def coefficient(field_hat: np.ndarray, k: tuple[int, int, int]) -> np.ndarray:
    n = field_hat.shape[1]
    return field_hat[(slice(None),) + index(k, n)]


def leray_project_all_modes(field_hat: np.ndarray) -> np.ndarray:
    """Project a sampled snapshot onto the discrete divergence-free carrier."""
    n = field_hat.shape[1]
    frequency = np.fft.fftfreq(n) * n
    kx, ky, kz = np.meshgrid(frequency, frequency, frequency, indexing="ij")
    norm_sq = kx * kx + ky * ky + kz * kz
    dot = kx * field_hat[0] + ky * field_hat[1] + kz * field_hat[2]
    projected = field_hat.copy()
    nonzero = norm_sq > 0.0
    for component, wave in enumerate((kx, ky, kz)):
        correction = np.zeros_like(dot)
        correction[nonzero] = wave[nonzero] * dot[nonzero] / norm_sq[nonzero]
        projected[component] -= correction
    return projected


def transfer(field_hat: np.ndarray, out: tuple[int, int, int], left: tuple[int, int, int], right: tuple[int, int, int]) -> float:
    out_k = np.asarray(out, dtype=np.float64)
    left_k = np.asarray(left, dtype=np.float64)
    right_k = np.asarray(right, dtype=np.float64)
    ul = coefficient(field_hat, left)
    ur = coefficient(field_hat, right)
    nonlinear = 1j * (np.dot(right_k, ul) * ur + np.dot(left_k, ur) * ul)
    return float(-np.real(np.vdot(coefficient(field_hat, out), projector(out_k, nonlinear))))


def helical_mismatch(field_hat: np.ndarray, modes: tuple[tuple[int, int, int], ...]) -> float:
    vortices = []
    for mode in modes:
        k = np.asarray(mode, dtype=np.float64)
        vortices.append(1j * np.cross(k, coefficient(field_hat, mode)))
    defects = []
    for i, j in ((0, 1), (0, 2), (1, 2)):
        denom = np.linalg.norm(vortices[i]) * np.linalg.norm(vortices[j])
        if denom <= 1.0e-30:
            continue
        defects.append(1.0 - abs(np.vdot(vortices[i], vortices[j])) / denom)
    return float(np.mean(defects)) if defects else math.nan


def modes(cutoff: int) -> list[tuple[int, int, int]]:
    return [
        (a, b, c)
        for a in range(-cutoff, cutoff + 1)
        for b in range(-cutoff, cutoff + 1)
        for c in range(-cutoff, cutoff + 1)
        if (a, b, c) != (0, 0, 0)
    ]


def main() -> None:
    args = parse_args()
    if args.cutoff <= 0 or args.max_triads <= 0:
        raise ValueError("cutoff and max-triads must be positive")
    velocity = load_velocity(args.raw_archive, args.frame)
    n = velocity.shape[1]
    if velocity.shape != (3, n, n, n):
        raise ValueError(f"expected (3,N,N,N), got {velocity.shape!r}")
    field_hat = leray_project_all_modes(
        np.fft.fftn(velocity, axes=(1, 2, 3)) / float(n ** 3)
    )
    pool = modes(args.cutoff)
    pool_set = set(pool)
    rows: list[dict[str, float]] = []
    # Canonical p <= q removes input swap duplication; r is fixed by zero sum.
    for p_index, p in enumerate(pool):
        for q in pool[p_index:]:
            r = tuple(-(p[i] + q[i]) for i in range(3))
            if r == (0, 0, 0) or r not in pool_set or q > r:
                continue
            transfers = np.asarray(
                [
                    # For p+q+r=0, the convolution output is -p with
                    # inputs q,r.  The Hermitian energy pairing against
                    # u_{-p} represents the modal energy of p by reality.
                    transfer(field_hat, tuple(-x for x in p), q, r),
                    transfer(field_hat, tuple(-x for x in q), r, p),
                    transfer(field_hat, tuple(-x for x in r), p, q),
                ]
            )
            conservation_error = abs(float(np.sum(transfers)))
            transfer_edge_sq = float(
                ((transfers[0] - transfers[1]) ** 2
                 + (transfers[0] - transfers[2]) ** 2
                 + (transfers[1] - transfers[2]) ** 2) / 3.0
            )
            transfer_scale = float(np.max(np.abs(transfers)))
            mismatch = helical_mismatch(field_hat, (p, q, r))
            modal_dissipation = float(sum(
                np.dot(mode, mode) * np.vdot(coefficient(field_hat, mode), coefficient(field_hat, mode)).real
                for mode in (p, q, r)
            ))
            if math.isfinite(mismatch) and modal_dissipation > 1.0e-30:
                rows.append({
                    "mismatch": mismatch,
                    "transfer_edge_sq": transfer_edge_sq,
                    "modal_dissipation": modal_dissipation,
                    "normalised_flux": transfer_edge_sq / modal_dissipation,
                    "good_edge_required_x": (
                        transfer_edge_sq / modal_dissipation / (mismatch * mismatch)
                        if mismatch > 1.0e-15 else math.inf
                    ),
                    "conservation_error": conservation_error,
                    "transfer_scale": transfer_scale,
                })
            if len(rows) >= args.max_triads:
                break
        if len(rows) >= args.max_triads:
            break
    if not rows:
        raise RuntimeError("no finite sampled triads")
    mismatch = np.asarray([row["mismatch"] for row in rows])
    flux = np.asarray([row["normalised_flux"] for row in rows])
    transfer_sq = np.asarray([row["transfer_edge_sq"] for row in rows])
    required_x = np.asarray([row["good_edge_required_x"] for row in rows])
    finite_required_x = required_x[np.isfinite(required_x)]
    total_flux = float(np.sum(flux))
    meaningful_scale = max(float(np.max([row["transfer_scale"] for row in rows])) * 1.0e-8, 1.0e-30)
    relative_conservation_errors = [
        row["conservation_error"] / row["transfer_scale"]
        for row in rows if row["transfer_scale"] >= meaningful_scale
    ]
    threshold_rows: list[dict[str, float]] = []
    for eta in sorted(set(float(value) for value in args.thresholds if 0.0 <= value <= 1.0)):
        bad = mismatch > eta
        threshold_rows.append({
            "eta": eta,
            "bad_fraction": float(np.mean(bad)),
            "bad_flux_fraction": float(np.sum(flux[bad]) / total_flux) if total_flux > 0.0 else math.nan,
            "good_flux_fraction": float(np.sum(flux[~bad]) / total_flux) if total_flux > 0.0 else math.nan,
            "bad_count": int(np.sum(bad)),
        })
    payload: dict[str, Any] = {
        "contract": "ns_triad_edge_depletion_audit",
        "authority": authority(),
        "status": "ok",
        "definition": {
            "defect": "mean_pairwise(1 - |<omega_a,omega_b>|/(|omega_a||omega_b|))",
            "normalised_flux": "edge_transfer_variation / modal_viscous_density",
            "warning": "This is one explicit helical-mismatch candidate, not the theorem-level delta_e or X_e.",
        },
        "inputs": {
            "raw_archive": str(args.raw_archive),
            "frame": args.frame,
            "cutoff": args.cutoff,
            "discrete_leray_projected": True,
        },
        "sample": {
            "triad_count": len(rows),
            "max_modal_conservation_error": float(max(row["conservation_error"] for row in rows)),
            "max_modal_transfer_scale": float(max(row["transfer_scale"] for row in rows)),
            "max_relative_modal_conservation_error_on_meaningful_triads": float(max(relative_conservation_errors)),
            "meaningful_transfer_scale_floor": meaningful_scale,
            "total_normalised_flux": total_flux,
            "mismatch_flux_pearson": float(np.corrcoef(mismatch, flux)[0, 1]) if len(rows) > 1 else math.nan,
            "mismatch_transfer_sq_pearson": float(np.corrcoef(mismatch, transfer_sq)[0, 1]) if len(rows) > 1 else math.nan,
            "good_edge_required_x_quantiles": {
                "p50": float(np.quantile(finite_required_x, 0.50)),
                "p90": float(np.quantile(finite_required_x, 0.90)),
                "p99": float(np.quantile(finite_required_x, 0.99)),
                "max": float(np.max(finite_required_x)),
            },
            "threshold_rows": threshold_rows,
        },
        "decision": "candidate-only calibration; no hierarchy or sparsity theorem inferred",
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(payload, indent=2, sort_keys=True, allow_nan=False) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2, sort_keys=True, allow_nan=False))


if __name__ == "__main__":
    main()
