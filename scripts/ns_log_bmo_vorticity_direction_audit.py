#!/usr/bin/env python3
"""Compute a finite multiscale log-BMO surrogate for packet vorticity direction.

This is a hypothesis-search companion to the coherence-budget audit.  For each
saved ``raw_hat`` checkpoint it reconstructs the target-shell vorticity
``omega_K`` and its direction ``xi_K``.  On periodic cubes of several grid
radii it computes an enstrophy-weighted local RMS direction oscillation and the
logarithmically weighted quantity

    |log(r/L)| * osc_r(xi_K),

which is the discrete diagnostic suggested by a ``bmo_{1/|log r|}``-type
criterion.  The diagnostic is not a proof that the continuum BMO hypothesis
holds: it samples a finite grid, finitely many cube sizes, and uses RMS rather
than the exact mean oscillation.  It is designed to discover scaling, compare
cutoffs, and falsify candidate uniform bounds.
"""
from __future__ import annotations

import argparse
import json
import math
import os
from pathlib import Path
import tempfile
from typing import Any

import numpy as np

SCRIPT_NAME = "scripts/ns_log_bmo_vorticity_direction_audit.py"


def parse_int_list(raw: str) -> tuple[int, ...]:
    values = tuple(sorted({int(token.strip()) for token in raw.split(",") if token.strip()}))
    if not values or any(value < 1 for value in values):
        raise ValueError("radii must be positive integers")
    return values


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--residence-json", type=Path, required=True)
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--grid-radii", default="1,2,4,8")
    parser.add_argument("--active-relative-floor", type=float, default=1.0e-12)
    parser.add_argument("--allow-missing-state", action="store_true")
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def atomic_json(path: Path, payload: dict[str, Any], pretty: bool = False) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        mode="w", encoding="utf-8", dir=path.parent,
        prefix=f".{path.name}.", suffix=".partial", delete=False,
    ) as handle:
        temporary = Path(handle.name)
        json.dump(payload, handle, indent=2 if pretty else None, sort_keys=True)
        handle.write("\n")
        handle.flush()
        os.fsync(handle.fileno())
    try:
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def frequency_grid(n: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    axis = np.fft.fftfreq(n) * n
    kz, ky, kx = np.meshgrid(axis, axis, axis, indexing="ij")
    wave = np.stack((kx, ky, kz), axis=-1)
    norm = np.sqrt(np.sum(wave * wave, axis=-1))
    dealias = np.all(np.abs(wave) <= float(n) / 3.0, axis=-1)
    return wave, norm, dealias


def packet_vorticity_direction(
    raw_hat: np.ndarray,
    target_shell: int,
    active_relative_floor: float,
) -> tuple[np.ndarray, np.ndarray]:
    if raw_hat.ndim != 4 or raw_hat.shape[-1] != 3 or len(set(raw_hat.shape[:3])) != 1:
        raise ValueError(f"expected raw_hat shape (N,N,N,3), got {raw_hat.shape!r}")
    n = int(raw_hat.shape[0])
    wave, norm, dealias = frequency_grid(n)
    packet = (
        (norm >= float(2 ** target_shell))
        & (norm < float(2 ** (target_shell + 1)))
        & dealias
    )
    packet_hat = raw_hat * packet[..., None]
    omega_hat = 1j * np.cross(wave, packet_hat)
    omega = np.fft.ifftn(omega_hat, axes=(0, 1, 2)).real
    omega_sq = np.sum(omega * omega, axis=-1)
    maximum = float(np.max(omega_sq)) if omega_sq.size else 0.0
    active = omega_sq > max(1.0e-30, active_relative_floor * maximum)
    weights = np.where(active, omega_sq, 0.0)
    if float(np.sum(weights)) <= 0.0:
        raise ValueError("target packet has zero active vorticity")
    xi = np.zeros_like(omega)
    xi[active] = omega[active] / np.sqrt(omega_sq[active])[:, None]
    return xi, weights


def periodic_box_sum(values: np.ndarray, radius: int) -> np.ndarray:
    result = values.astype(np.float64, copy=True)
    for axis in range(3):
        base = result
        result = np.zeros_like(base)
        for shift in range(-radius, radius + 1):
            result += np.roll(base, shift, axis=axis)
    return result


def multiscale_direction_oscillation(
    xi: np.ndarray,
    weights: np.ndarray,
    radii: tuple[int, ...],
) -> dict[str, Any]:
    if xi.shape[:-1] != weights.shape or xi.shape[-1] != 3:
        raise ValueError("xi and weights shapes are incompatible")
    n = int(weights.shape[0])
    if len(set(weights.shape)) != 1:
        raise ValueError("expected a cubic grid")
    rows: list[dict[str, float | int | bool]] = []
    for requested_radius in radii:
        radius = min(requested_radius, max((n - 1) // 2, 1))
        denominator = periodic_box_sum(weights, radius)
        means = np.zeros_like(xi)
        for component in range(3):
            numerator = periodic_box_sum(weights * xi[..., component], radius)
            means[..., component] = np.divide(
                numerator,
                denominator,
                out=np.zeros_like(numerator),
                where=denominator > 1.0e-30,
            )
        # Since |xi|=1 on the active set, the weighted local second central
        # moment is 1-|E xi|^2.  Its square root upper-bounds mean oscillation.
        mean_norm_sq = np.sum(means * means, axis=-1)
        local_rms = np.sqrt(np.maximum(1.0 - mean_norm_sq, 0.0))
        valid = denominator > 1.0e-30
        window_side = 2 * radius + 1
        relative_scale = min(float(window_side) / float(n), 1.0 - 1.0e-15)
        log_weight = abs(math.log(relative_scale))
        maximum = float(np.max(local_rms[valid])) if np.any(valid) else 0.0
        weighted_average = (
            float(np.sum(denominator[valid] * local_rms[valid]) / np.sum(denominator[valid]))
            if np.any(valid) else 0.0
        )
        rows.append({
            "requested_grid_radius": requested_radius,
            "grid_radius": radius,
            "window_side": window_side,
            "relative_scale": relative_scale,
            "log_weight": log_weight,
            "maximum_local_rms_direction_oscillation": maximum,
            "weighted_average_local_rms_direction_oscillation": weighted_average,
            "log_weighted_maximum_oscillation": log_weight * maximum,
            "radius_clamped": radius != requested_radius,
        })
    return {
        "scale_rows": rows,
        "log_bmo_surrogate_sup": max(float(row["log_weighted_maximum_oscillation"]) for row in rows),
        "unweighted_multiscale_oscillation_sup": max(float(row["maximum_local_rms_direction_oscillation"]) for row in rows),
    }


def checkpoint_metric(
    state_path: Path,
    target_shell: int,
    radii: tuple[int, ...],
    active_relative_floor: float,
) -> dict[str, Any]:
    with np.load(state_path, allow_pickle=False) as data:
        raw = np.asarray(data["raw_hat"], dtype=np.complex128)
    xi, weights = packet_vorticity_direction(raw, target_shell, active_relative_floor)
    result = multiscale_direction_oscillation(xi, weights, radii)
    result.update({
        "cutoff": int(raw.shape[0]),
        "target_shell": target_shell,
        "active_enstrophy_sum": float(np.sum(weights)),
        "active_grid_fraction": float(np.mean(weights > 0.0)),
    })
    return result


def audit(
    residence_payload: dict[str, Any],
    radii: tuple[int, ...],
    active_relative_floor: float,
    allow_missing_state: bool,
) -> dict[str, Any]:
    checkpoints = residence_payload.get("checkpoints")
    if not isinstance(checkpoints, list) or not checkpoints:
        raise ValueError("residence JSON has no nonempty checkpoints list")
    if not math.isfinite(active_relative_floor) or not (0.0 < active_relative_floor < 1.0):
        raise ValueError("active-relative-floor must lie in (0,1)")

    rows: list[dict[str, Any]] = []
    cutoff_values: dict[int, list[float]] = {}
    for index, checkpoint in enumerate(checkpoints):
        if not isinstance(checkpoint, dict):
            raise ValueError("checkpoint rows must be objects")
        state_path = Path(str(checkpoint.get("source_state", "")))
        target_shell = int(checkpoint["target_shell"])
        try:
            metric = checkpoint_metric(state_path, target_shell, radii, active_relative_floor)
        except (FileNotFoundError, KeyError, ValueError) as exc:
            if not allow_missing_state:
                raise
            metric = None
            state_error = str(exc)
        else:
            state_error = None
            cutoff_values.setdefault(int(metric["cutoff"]), []).append(float(metric["log_bmo_surrogate_sup"]))
        rows.append({
            "checkpoint_index": int(checkpoint.get("checkpoint_index", index)),
            "trajectory_id": str(checkpoint.get("trajectory_id", "aggregate-trajectory")),
            "source_state": str(state_path),
            "time": float(checkpoint.get("time", index)),
            "gamma": checkpoint.get("gamma"),
            "packet_tight": bool(checkpoint.get("packet_tight", False)),
            "log_bmo_metric": metric,
            "metric_available": metric is not None,
            "state_error": state_error,
            "truth_authority": False,
            "theorem_authority": False,
            "promoted": False,
        })

    cutoff_summary = [
        {
            "cutoff": cutoff,
            "checkpoint_count": len(values),
            "maximum_log_bmo_surrogate": max(values),
            "minimum_log_bmo_surrogate": min(values),
            "mean_log_bmo_surrogate": float(np.mean(values)),
        }
        for cutoff, values in sorted(cutoff_values.items())
    ]
    return {
        "schema_version": "1.0.0",
        "script": SCRIPT_NAME,
        "authority": {
            "candidate_only": True,
            "finite_grid_surrogate": True,
            "continuum_log_bmo_hypothesis_proved": False,
            "cutoff_uniform_authority": False,
            "truth_authority": False,
            "theorem_authority": False,
            "bkm_authority": False,
            "clay_authority": False,
            "promoted": False,
        },
        "definition": {
            "direction": "target-shell vorticity direction",
            "local_oscillation": "enstrophy-weighted periodic-cube RMS direction oscillation",
            "log_weight": "absolute log of cube side divided by box side",
            "log_bmo_surrogate": "sup over requested radii of log_weight times maximum local RMS oscillation",
            "grid_radii": list(radii),
            "active_relative_floor": active_relative_floor,
        },
        "checkpoints": rows,
        "cutoff_summary": cutoff_summary,
        "cutoff_count": len(cutoff_summary),
        "uniform_candidate_tested_across_multiple_cutoffs": len(cutoff_summary) >= 2,
        "limitations": [
            "finite periodic grid and finitely many cube sizes",
            "RMS oscillation is a computable upper proxy, not exact BMO mean oscillation",
            "target-shell projection differs from the full vorticity-direction hypothesis",
            "no bound between sampled radii or between saved times",
            "no cutoff-uniform, BKM, or Clay authority",
        ],
    }


def main() -> None:
    args = parse_args()
    payload = json.loads(args.residence_json.read_text(encoding="utf-8"))
    result = audit(
        payload,
        parse_int_list(args.grid_radii),
        args.active_relative_floor,
        args.allow_missing_state,
    )
    atomic_json(args.output_json, result, args.pretty)
    print(json.dumps({
        "output_json": str(args.output_json),
        "checkpoint_count": len(result["checkpoints"]),
        "available_count": sum(bool(row["metric_available"]) for row in result["checkpoints"]),
        "cutoff_count": result["cutoff_count"],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
