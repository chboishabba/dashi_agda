#!/usr/bin/env python3
"""Candidate-only Fourier triad-edge depletion audit.

The primary candidate is the exact helical phase-saturation defect.  Each
modal Fourier transfer is decomposed into its eight helical-channel terms;
each transfer-difference edge is therefore a finite signed sum.  Its defect

  delta_sat = |sum(channel terms)| / sum(|channel terms|)

measures cancellation in the *same cubic interaction* used by the physical
edge-transfer lane.  Consequently the local identity

  |Delta T|^2 / d = delta_sat^2 * (A^2 / d^2) * d

is numerical algebra, not a proposed NS estimate.  What remains empirical is
whether high-saturation edges have small instantaneous or temporal flux mass.
This script is a falsification diagnostic only; it proves no hierarchy,
sparsity, regularity, or Clay claim.
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
    "ns_triad_edge_phase_saturation_audit_N128_20260716.json"
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_ARCHIVE)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--frame", type=int, default=0,
                        help="backward-compatible single frame when --frames is absent")
    parser.add_argument("--frames", type=int, nargs="*", default=None,
                        help="snapshot indices; enables snapshot-weighted residence summaries")
    parser.add_argument("--cutoff", type=int, default=8)
    parser.add_argument("--max-triads", type=int, default=12000)
    parser.add_argument("--thresholds", type=float, nargs="*", default=(0.1, 0.25, 0.5, 0.75, 0.9, 0.95, 0.99))
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


def helical_basis(mode: tuple[int, int, int]) -> tuple[np.ndarray, np.ndarray]:
    """Deterministic Waleffe frame satisfying i k×h^s = s |k| h^s."""
    k = np.asarray(mode, dtype=np.float64)
    norm = float(np.linalg.norm(k))
    if norm == 0.0:
        raise ValueError("zero mode has no helical basis")
    khat = k / norm
    # Pick the least parallel coordinate axis, making the frame deterministic.
    axis = np.eye(3)[int(np.argmin(np.abs(khat)))]
    e1 = np.cross(khat, axis)
    e1 /= np.linalg.norm(e1)
    e2 = np.cross(khat, e1)
    h_plus = (e1 + 1j * e2) / math.sqrt(2.0)
    h_minus = (e1 - 1j * e2) / math.sqrt(2.0)
    return h_plus, h_minus


def helical_components(value: np.ndarray, mode: tuple[int, int, int]) -> tuple[np.ndarray, np.ndarray]:
    """Return the two projected helical components of a divergence-free mode."""
    h_plus, h_minus = helical_basis(mode)
    return np.vdot(h_plus, value) * h_plus, np.vdot(h_minus, value) * h_minus


def transfer_helical_terms(
    field_hat: np.ndarray,
    out: tuple[int, int, int],
    left: tuple[int, int, int],
    right: tuple[int, int, int],
) -> np.ndarray:
    """Eight real channel terms summing to ``transfer(field_hat, out, left, right)``.

    The output test coefficient and both input coefficients are decomposed in
    their own deterministic helical frames.  Projecting each channel makes
    this an exact decomposition of the implementation's symmetrized transfer,
    up to floating-point projection/reconstruction error.
    """
    out_k = np.asarray(out, dtype=np.float64)
    left_k = np.asarray(left, dtype=np.float64)
    right_k = np.asarray(right, dtype=np.float64)
    out_components = helical_components(coefficient(field_hat, out), out)
    left_components = helical_components(coefficient(field_hat, left), left)
    right_components = helical_components(coefficient(field_hat, right), right)
    terms = []
    for u_out in out_components:
        for u_left in left_components:
            for u_right in right_components:
                nonlinear = 1j * (
                    np.dot(right_k, u_left) * u_right
                    + np.dot(left_k, u_right) * u_left
                )
                terms.append(float(-np.real(np.vdot(u_out, projector(out_k, nonlinear)))))
    return np.asarray(terms, dtype=np.float64)


def modes(cutoff: int) -> list[tuple[int, int, int]]:
    return [
        (a, b, c)
        for a in range(-cutoff, cutoff + 1)
        for b in range(-cutoff, cutoff + 1)
        for c in range(-cutoff, cutoff + 1)
        if (a, b, c) != (0, 0, 0)
    ]


def canonical_triads(cutoff: int, max_triads: int) -> list[tuple[tuple[int, int, int], tuple[int, int, int], tuple[int, int, int]]]:
    pool = modes(cutoff)
    pool_set = set(pool)
    triads = []
    # p <= q <= r chooses one representative of each labelled geometric triad.
    for p_index, p in enumerate(pool):
        for q in pool[p_index:]:
            r = tuple(-(p[i] + q[i]) for i in range(3))
            if r == (0, 0, 0) or r not in pool_set or q > r:
                continue
            triads.append((p, q, r))
            if len(triads) >= max_triads:
                return triads
    return triads


def edge_saturation(terms_a: np.ndarray, terms_b: np.ndarray) -> tuple[float, float, float]:
    """Return Delta T, its helical absolute envelope, and saturation defect."""
    # Concatenation is the exact common finite channel carrier for T_a - T_b.
    signed_terms = np.concatenate((terms_a, -terms_b))
    delta = float(np.sum(signed_terms))
    envelope = float(np.sum(np.abs(signed_terms)))
    saturation = abs(delta) / envelope if envelope > 1.0e-30 else 0.0
    return delta, envelope, saturation


def audit_frame(
    field_hat: np.ndarray,
    triads: list[tuple[tuple[int, int, int], tuple[int, int, int]]],
    frame: int,
) -> list[dict[str, float]]:
    rows: list[dict[str, float]] = []
    for p, q, r in triads:
        modal_terms = (
            transfer_helical_terms(field_hat, tuple(-x for x in p), q, r),
            transfer_helical_terms(field_hat, tuple(-x for x in q), r, p),
            transfer_helical_terms(field_hat, tuple(-x for x in r), p, q),
        )
        transfers = np.asarray([np.sum(terms) for terms in modal_terms])
        direct_transfers = np.asarray([
            transfer(field_hat, tuple(-x for x in p), q, r),
            transfer(field_hat, tuple(-x for x in q), r, p),
            transfer(field_hat, tuple(-x for x in r), p, q),
        ])
        reconstruction_error = float(np.max(np.abs(transfers - direct_transfers)))
        conservation_error = abs(float(np.sum(transfers)))
        edges = (
            edge_saturation(modal_terms[0], modal_terms[1]),
            edge_saturation(modal_terms[0], modal_terms[2]),
            edge_saturation(modal_terms[1], modal_terms[2]),
        )
        transfer_edge_sq = float(sum(delta * delta for delta, _, _ in edges) / 3.0)
        transfer_scale = float(np.max(np.abs(transfers)))
        mismatch = helical_mismatch(field_hat, (p, q, r))
        modal_dissipation = float(sum(
            np.dot(mode, mode) * np.vdot(coefficient(field_hat, mode), coefficient(field_hat, mode)).real
            for mode in (p, q, r)
        ))
        if modal_dissipation <= 1.0e-30:
            continue
        edge_fluxes = np.asarray([delta * delta / modal_dissipation for delta, _, _ in edges])
        saturations = np.asarray([saturation for _, _, saturation in edges])
        envelopes = np.asarray([envelope for _, envelope, _ in edges])
        # This is the exact local hierarchy factor X_env for d=modal_dissipation.
        x_env = envelopes * envelopes / (modal_dissipation * modal_dissipation)
        local_identity_errors = np.abs(
            edge_fluxes - saturations * saturations * x_env * modal_dissipation
        )
        for edge_index in range(3):
            rows.append({
                "frame": frame,
                "edge": edge_index,
                "saturation": float(saturations[edge_index]),
                "envelope": float(envelopes[edge_index]),
                "x_env": float(x_env[edge_index]),
                "edge_flux": float(edge_fluxes[edge_index]),
                "local_identity_error": float(local_identity_errors[edge_index]),
                "modal_dissipation": modal_dissipation,
                "helical_reconstruction_error": reconstruction_error,
                "conservation_error": conservation_error,
                "transfer_scale": transfer_scale,
                "mismatch": mismatch,
            })
    return rows


def main() -> None:
    args = parse_args()
    if args.cutoff <= 0 or args.max_triads <= 0:
        raise ValueError("cutoff and max-triads must be positive")
    with np.load(args.raw_archive, allow_pickle=False) as data:
        snapshot_count = int(np.asarray(data["velocity_snapshots"]).shape[0])
    frames = args.frames if args.frames is not None and len(args.frames) else [args.frame]
    if any(frame < 0 or frame >= snapshot_count for frame in frames):
        raise ValueError(f"frames must lie in [0, {snapshot_count})")
    triads = canonical_triads(args.cutoff, args.max_triads)
    if not triads:
        raise RuntimeError("no canonical cutoff triads")
    rows: list[dict[str, float]] = []
    n = 0
    for frame in frames:
        velocity = load_velocity(args.raw_archive, frame)
        n = velocity.shape[1]
        if velocity.shape != (3, n, n, n):
            raise ValueError(f"expected (3,N,N,N), got {velocity.shape!r}")
        field_hat = leray_project_all_modes(
            np.fft.fftn(velocity, axes=(1, 2, 3)) / float(n ** 3)
        )
        rows.extend(audit_frame(field_hat, triads, frame))
    if not rows:
        raise RuntimeError("no finite sampled triads")
    saturation = np.asarray([row["saturation"] for row in rows])
    flux = np.asarray([row["edge_flux"] for row in rows])
    x_env = np.asarray([row["x_env"] for row in rows])
    mismatch = np.asarray([row["mismatch"] for row in rows])
    total_flux = float(np.sum(flux))
    meaningful_scale = max(float(np.max([row["transfer_scale"] for row in rows])) * 1.0e-8, 1.0e-30)
    relative_conservation_errors = [
        row["conservation_error"] / row["transfer_scale"]
        for row in rows if row["transfer_scale"] >= meaningful_scale
    ]
    threshold_rows: list[dict[str, float]] = []
    for eta in sorted(set(float(value) for value in args.thresholds if 0.0 <= value <= 1.0)):
        bad = saturation > eta
        threshold_rows.append({
            "eta": eta,
            "bad_edge_fraction": float(np.mean(bad)),
            "bad_flux_fraction": float(np.sum(flux[bad]) / total_flux) if total_flux > 0.0 else math.nan,
            "good_flux_fraction": float(np.sum(flux[~bad]) / total_flux) if total_flux > 0.0 else math.nan,
            "bad_count": int(np.sum(bad)),
        })
    frame_residence = []
    for frame in frames:
        frame_mask = np.asarray([row["frame"] == frame for row in rows])
        frame_flux = flux[frame_mask]
        frame_sat = saturation[frame_mask]
        frame_total = float(np.sum(frame_flux))
        frame_residence.append({
            "frame": frame,
            "total_edge_flux": frame_total,
            "bad_flux_fractions": {
                str(eta): float(np.sum(frame_flux[frame_sat > eta]) / frame_total) if frame_total > 0.0 else math.nan
                for eta in sorted(set(float(value) for value in args.thresholds if 0.0 <= value <= 1.0))
            },
        })
    payload: dict[str, Any] = {
        "contract": "ns_triad_edge_depletion_audit",
        "authority": authority(),
        "status": "ok",
        "definition": {
            "defect": "delta_sat(e) = |Delta T_e| / A_e, where A_e is the sum of absolute exact helical-channel terms",
            "channel_carrier": "eight helical terms per modal transfer; each edge is the concatenated 16-term difference carrier",
            "local_identity": "edge_flux = delta_sat^2 * x_env * modal_dissipation, x_env = A_e^2/modal_dissipation^2",
            "warning": "The identity does not establish a controllable global X or phase-saturation sparsity theorem.",
        },
        "inputs": {
            "raw_archive": str(args.raw_archive),
            "frames": frames,
            "cutoff": args.cutoff,
            "canonical_triad_count_per_frame": len(triads),
            "discrete_leray_projected": True,
        },
        "sample": {
            "edge_count": len(rows),
            "max_modal_conservation_error": float(max(row["conservation_error"] for row in rows)),
            "max_modal_transfer_scale": float(max(row["transfer_scale"] for row in rows)),
            "max_relative_modal_conservation_error_on_meaningful_triads": float(max(relative_conservation_errors)),
            "max_helical_reconstruction_error": float(max(row["helical_reconstruction_error"] for row in rows)),
            "max_local_identity_error": float(max(row["local_identity_error"] for row in rows)),
            "meaningful_transfer_scale_floor": meaningful_scale,
            "total_normalised_edge_flux": total_flux,
            "saturation_flux_pearson": float(np.corrcoef(saturation, flux)[0, 1]) if len(rows) > 1 else math.nan,
            "saturation_x_env_pearson": float(np.corrcoef(saturation, x_env)[0, 1]) if len(rows) > 1 else math.nan,
            "legacy_mismatch_flux_pearson": float(np.corrcoef(mismatch, flux)[0, 1]) if len(rows) > 1 else math.nan,
            "x_env_quantiles": {
                "p50": float(np.quantile(x_env, 0.50)),
                "p90": float(np.quantile(x_env, 0.90)),
                "p99": float(np.quantile(x_env, 0.99)),
                "max": float(np.max(x_env)),
            },
            "threshold_rows": threshold_rows,
            "snapshot_weighted_bad_flux_residence": frame_residence,
        },
        "decision": "candidate-only phase-saturation calibration; no hierarchy, bad-edge sparsity, temporal residence, or NS theorem inferred",
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(payload, indent=2, sort_keys=True, allow_nan=False) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2, sort_keys=True, allow_nan=False))


if __name__ == "__main__":
    main()
