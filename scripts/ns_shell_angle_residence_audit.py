#!/usr/bin/env python3
"""Audit shell/angle packet tightness and time-integrated Gamma residence.

This script consumes aggregate receipts produced by
``ns_triad_gamma_gap_raw_hat_export.py --aggregate-only``.  Sparse selected-mode
carriers are deliberately not reconstructed.  Instead, each receipt is paired
with its saved ``raw_hat`` state, the full packet dissipation is recomputed, and
we evaluate

    Gamma_K(t) = max(Q_K(t), 0) / (2 nu D_K(t)).

The coarse shell/angle gross-transfer census is used only to state an explicit
packet-tightness condition.  Duration-weighted dangerous-set and contiguous
residence statistics are then reported for configurable Gamma thresholds.

All output is empirical and fail-closed.  It is not a cutoff-uniform estimate,
a compactness theorem, a BKM theorem, or Clay authority.
"""
from __future__ import annotations

import argparse
import json
import math
import os
from dataclasses import dataclass
from pathlib import Path
import tempfile
from typing import Any, Iterable

import numpy as np

SCRIPT_NAME = "scripts/ns_shell_angle_residence_audit.py"


def parse_float_list(raw: str) -> tuple[float, ...]:
    values = tuple(sorted({float(token.strip()) for token in raw.split(",") if token.strip()}))
    if not values or any(not math.isfinite(value) or value < 0.0 for value in values):
        raise ValueError("thresholds must be finite and nonnegative")
    return values


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-json", type=Path, required=True)
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--gamma-thresholds", default="0.5,0.9,1.0")
    parser.add_argument("--tightness-radius", type=int, default=1,
                        help="require |p-shell offset| and |q-shell offset| <= this radius")
    parser.add_argument("--minimum-tightness", type=float, default=0.8)
    parser.add_argument("--duration-c", type=float, default=None,
                        help="override each checkpoint's parabolic duration c")
    parser.add_argument("--allow-missing-state", action="store_true",
                        help="emit unavailable Gamma rows instead of failing when raw_hat is absent")
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


def packet_dissipation_from_state(state_path: Path, target_shell: int) -> dict[str, float | int]:
    with np.load(state_path, allow_pickle=False) as data:
        raw = np.asarray(data["raw_hat"], dtype=np.complex128)
        nu = float(data["nu"]) if "nu" in data else 1.0e-3
        duration_c = float(data["segment_window_c"]) if "segment_window_c" in data else 0.05
    if raw.ndim != 4 or raw.shape[-1] != 3 or len(set(raw.shape[:3])) != 1:
        raise ValueError(f"{state_path}: expected raw_hat shape (N,N,N,3), got {raw.shape!r}")
    n = int(raw.shape[0])
    field = np.moveaxis(raw / float(n ** 3), -1, 0)
    axis = np.fft.fftfreq(n) * n
    kz, ky, kx = np.meshgrid(axis, axis, axis, indexing="ij")
    norm_sq = kx * kx + ky * ky + kz * kz
    norm = np.sqrt(norm_sq)
    dealias = (np.abs(kx) <= n / 3.0) & (np.abs(ky) <= n / 3.0) & (np.abs(kz) <= n / 3.0)
    packet = (norm >= float(2 ** target_shell)) & (norm < float(2 ** (target_shell + 1))) & dealias
    modal_energy = np.sum(np.abs(field) ** 2, axis=0)
    energy = float(np.sum(modal_energy[packet]))
    dissipation = float(np.sum(norm_sq[packet] * modal_energy[packet]))
    return {
        "cutoff": n,
        "physical_viscosity": nu,
        "segment_window_c": duration_c,
        "full_packet_energy": energy,
        "full_packet_dissipation": dissipation,
    }


def normalized_groups(groups: Iterable[dict[str, Any]]) -> list[dict[str, float | int]]:
    rows: list[dict[str, float | int]] = []
    total = 0.0
    for group in groups:
        try:
            gross = float(group["gross_activity"])
            p = int(group["p_shell_offset"])
            q = int(group["q_shell_offset"])
            angle = int(group["angle_bin"])
        except (KeyError, TypeError, ValueError) as exc:
            raise ValueError(f"malformed coarse shell/angle group: {group!r}") from exc
        if not math.isfinite(gross) or gross < 0.0:
            raise ValueError("gross shell/angle activity must be finite and nonnegative")
        rows.append({"p_shell_offset": p, "q_shell_offset": q, "angle_bin": angle,
                     "gross_activity": gross})
        total += gross
    if total <= 0.0:
        raise ValueError("coarse shell/angle census has zero gross activity")
    for row in rows:
        row["mass_fraction"] = float(row["gross_activity"]) / total
    return rows


def packet_geometry(groups: Iterable[dict[str, Any]], radius: int) -> dict[str, float | int]:
    rows = normalized_groups(groups)
    probabilities = np.asarray([float(row["mass_fraction"]) for row in rows], dtype=np.float64)
    tightness = sum(
        float(row["mass_fraction"])
        for row in rows
        if abs(int(row["p_shell_offset"])) <= radius and abs(int(row["q_shell_offset"])) <= radius
    )
    positive = probabilities[probabilities > 0.0]
    entropy = float(-np.sum(positive * np.log(positive)))
    effective_group_count = float(1.0 / np.sum(probabilities * probabilities))
    return {
        "group_count": len(rows),
        "tightness_radius": radius,
        "local_shell_mass_fraction": tightness,
        "largest_group_mass_fraction": float(np.max(probabilities)),
        "effective_group_count": effective_group_count,
        "shannon_entropy": entropy,
        "normalized_entropy": entropy / math.log(len(rows)) if len(rows) > 1 else 0.0,
    }


@dataclass(frozen=True)
class IntervalRow:
    trajectory_id: str
    time: float
    duration: float
    parabolic_duration: float
    gamma: float | None
    tight: bool


def contiguous_residence(rows: list[IntervalRow], threshold: float) -> dict[str, float | int | None]:
    dangerous_duration = 0.0
    dangerous_parabolic_duration = 0.0
    eligible_duration = 0.0
    integrated_gamma = 0.0
    integrated_excess = 0.0
    longest = 0.0
    longest_parabolic = 0.0
    current = 0.0
    current_parabolic = 0.0
    dangerous_count = 0
    eligible_count = 0
    for row in rows:
        eligible = row.tight and row.gamma is not None and math.isfinite(row.gamma)
        dangerous = eligible and float(row.gamma) >= threshold
        if eligible:
            eligible_count += 1
            eligible_duration += row.duration
            integrated_gamma += float(row.gamma) * row.duration
            integrated_excess += max(float(row.gamma) - threshold, 0.0) * row.duration
        if dangerous:
            dangerous_count += 1
            dangerous_duration += row.duration
            dangerous_parabolic_duration += row.parabolic_duration
            current += row.duration
            current_parabolic += row.parabolic_duration
            longest = max(longest, current)
            longest_parabolic = max(longest_parabolic, current_parabolic)
        else:
            current = 0.0
            current_parabolic = 0.0
    return {
        "gamma_threshold": threshold,
        "eligible_checkpoint_count": eligible_count,
        "dangerous_checkpoint_count": dangerous_count,
        "eligible_duration": eligible_duration,
        "dangerous_duration": dangerous_duration,
        "dangerous_duration_fraction": dangerous_duration / eligible_duration if eligible_duration > 0.0 else None,
        "dangerous_parabolic_duration": dangerous_parabolic_duration,
        "longest_contiguous_dangerous_duration": longest,
        "longest_contiguous_dangerous_parabolic_duration": longest_parabolic,
        "eligible_time_average_gamma": integrated_gamma / eligible_duration if eligible_duration > 0.0 else None,
        "integrated_positive_excess_above_threshold": integrated_excess,
    }


def audit(payload: dict[str, Any], thresholds: tuple[float, ...], radius: int,
          minimum_tightness: float, duration_override: float | None,
          allow_missing_state: bool) -> dict[str, Any]:
    receipts = payload.get("export_receipts")
    if not isinstance(receipts, list) or not receipts:
        raise ValueError("input JSON has no nonempty export_receipts list")
    if radius < 0 or not (0.0 <= minimum_tightness <= 1.0):
        raise ValueError("invalid tightness parameters")

    checkpoint_rows: list[dict[str, Any]] = []
    intervals_by_trajectory: dict[str, list[IntervalRow]] = {}
    next_time: dict[str, float] = {}
    for index, receipt in enumerate(receipts):
        if not isinstance(receipt, dict):
            raise ValueError("every export receipt must be an object")
        source_state = Path(str(receipt.get("source_state", "")))
        target_shell = int(receipt["target_shell"])
        trajectory_id = str(receipt.get("trajectory_id", payload.get("trajectory_id", "aggregate-trajectory")))
        geometry = packet_geometry(receipt.get("coarse_shell_angle_groups", []), radius)
        tight = float(geometry["local_shell_mass_fraction"]) >= minimum_tightness
        state_metrics: dict[str, float | int] | None
        try:
            state_metrics = packet_dissipation_from_state(source_state, target_shell)
        except (FileNotFoundError, KeyError, ValueError) as exc:
            if not allow_missing_state:
                raise
            state_metrics = None
            state_error = str(exc)
        else:
            state_error = None

        signed_rate = float(receipt["full_packet_signed_rate"])
        gross = float(receipt["full_packet_gross_activity"])
        gamma: float | None = None
        physical_duration = 0.0
        parabolic_duration = 0.0
        cutoff: int | None = None
        dissipation: float | None = None
        nu: float | None = None
        if state_metrics is not None:
            nu = float(state_metrics["physical_viscosity"])
            dissipation = float(state_metrics["full_packet_dissipation"])
            cutoff = int(state_metrics["cutoff"])
            c = duration_override if duration_override is not None else float(state_metrics["segment_window_c"])
            if c <= 0.0 or nu <= 0.0:
                raise ValueError("duration-c and viscosity must be positive")
            parabolic_duration = c
            physical_duration = c * (2.0 ** (-2 * target_shell)) / nu
            gamma = max(signed_rate, 0.0) / (2.0 * nu * dissipation) if dissipation > 0.0 else None

        time = float(receipt.get("time", next_time.get(trajectory_id, 0.0)))
        next_time[trajectory_id] = time + physical_duration
        cancellation_ratio = signed_rate / gross if gross > 0.0 else None
        row = {
            "checkpoint_index": index,
            "source_state": str(source_state),
            "trajectory_id": trajectory_id,
            "time": time,
            "duration": physical_duration,
            "parabolic_duration": parabolic_duration,
            "target_shell": target_shell,
            "cutoff": cutoff,
            "physical_viscosity": nu,
            "full_packet_signed_rate": signed_rate,
            "full_packet_gross_activity": gross,
            "signed_to_gross_ratio": cancellation_ratio,
            "positive_signed_to_gross_ratio": max(signed_rate, 0.0) / gross if gross > 0.0 else None,
            "full_packet_dissipation": dissipation,
            "gamma": gamma,
            "packet_geometry": geometry,
            "minimum_tightness": minimum_tightness,
            "packet_tight": tight,
            "gamma_available": gamma is not None,
            "state_error": state_error,
            "truth_authority": False,
            "theorem_authority": False,
            "promoted": False,
        }
        checkpoint_rows.append(row)
        intervals_by_trajectory.setdefault(trajectory_id, []).append(
            IntervalRow(trajectory_id, time, physical_duration, parabolic_duration, gamma, tight)
        )

    trajectory_audits: list[dict[str, Any]] = []
    for trajectory_id, rows in sorted(intervals_by_trajectory.items()):
        rows.sort(key=lambda row: row.time)
        trajectory_audits.append({
            "trajectory_id": trajectory_id,
            "checkpoint_count": len(rows),
            "threshold_audits": [contiguous_residence(rows, threshold) for threshold in thresholds],
        })

    return {
        "schema_version": "1.0.0",
        "script": SCRIPT_NAME,
        "authority": {
            "candidate_only": True,
            "empirical_non_promoting": True,
            "truth_authority": False,
            "theorem_authority": False,
            "bkm_authority": False,
            "clay_authority": False,
            "promoted": False,
        },
        "definition": {
            "gamma": "max(full_packet_signed_rate,0)/(2*nu*full_packet_dissipation)",
            "packet_tightness": "gross shell-angle mass with |p_offset|,|q_offset| <= radius",
            "tightness_radius": radius,
            "minimum_tightness": minimum_tightness,
            "gamma_thresholds": list(thresholds),
        },
        "checkpoints": checkpoint_rows,
        "trajectories": trajectory_audits,
        "limitations": [
            "finite saved Galerkin checkpoints only",
            "piecewise-constant residence uses saved checkpoint durations",
            "packet tightness is a coarse shell-offset condition, not compactness",
            "no cutoff-uniform constant is inferred",
            "no residence estimate for unseen times is inferred",
            "no BKM or Clay promotion",
        ],
    }


def main() -> None:
    args = parse_args()
    payload = json.loads(args.input_json.read_text(encoding="utf-8"))
    result = audit(payload, parse_float_list(args.gamma_thresholds), args.tightness_radius,
                   args.minimum_tightness, args.duration_c, args.allow_missing_state)
    atomic_json(args.output_json, result, args.pretty)
    print(json.dumps({
        "output_json": str(args.output_json),
        "checkpoint_count": len(result["checkpoints"]),
        "trajectory_count": len(result["trajectories"]),
        "gamma_available_count": sum(bool(row["gamma_available"]) for row in result["checkpoints"]),
    }, sort_keys=True))


if __name__ == "__main__":
    main()
