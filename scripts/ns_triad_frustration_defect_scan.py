#!/usr/bin/env python3
"""Scan candidate triad phase-frustration defects on the raw N128 archive.

The artifact is empirical and candidate-only.  It does not promote any theorem,
Clay claim, or proof boundary.  It loads the same raw archive used by the orbit
and coherence scans, reuses the dominant-mode selection conventions where
practical, and then builds resonant triads on each frame.

For each selected frame it emits a finite-dimensional frustration proxy based on
a low-order fitted phase field and weighted residuals on resonant triad phase
closures.  The output is intentionally fail-closed: malformed inputs or
non-finite arithmetic are reported explicitly rather than hidden.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np

from ns_boundary_pressure_gate_scan import _frame_indices, _pearson  # type: ignore
from ns_orbit_phase_coherence_scan import (  # type: ignore
    AUTHORITY,
    ModeRecord,
    _collect_modes,
    _frame_velocity,
    _json_text,
    _load_raw_bundle,
    _scalar_vorticity_spectrum,
)


SCRIPT_NAME = "scripts/ns_triad_frustration_defect_scan.py"
CONTRACT = "ns_triad_frustration_defect_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_FRUSTRATION_DEFECT_SCAN"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, ERROR_STATUS}

DEFAULT_RAW_ARCHIVE = Path(
    "/home/c/Documents/code/dashiCFD/outputs/"
    "sprint65_pressure_reconstruction_N128_seed0_gpu/ns3d_N128_seed0_gpu_pressure.npz"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_frustration_defect_scan_N128_20260621.json"
)
DEFAULT_TOP_K = 48
DEFAULT_POOL_MULTIPLIER = 24
DEFAULT_ZERO_EPS = 1.0e-12

CONTROL_CARD = {
    "O": "Measure candidate triad phase-frustration telemetry on the raw N128 archive.",
    "R": (
        "Build resonant selected-mode triads, fit a low-dimensional phase field, "
        "and summarize weighted phase-closure frustration together with coherence-loss proxies."
    ),
    "C": SCRIPT_NAME,
    "S": "Empirical scan only; malformed inputs and non-finite arithmetic are fail-closed errors.",
    "L": (
        "Load raw frames, select dominant modes, construct resonant triads, "
        "fit a finite-dimensional phase field, and emit framewise plus aggregate telemetry."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, Clay, or promotion claim is inferred from this scan.",
    "F": "All outputs are candidate-only empirical telemetry and remain non-promoting.",
}


@dataclass(frozen=True)
class TriadRecord:
    left: int
    right: int
    out: int
    weight: float
    closure: float
    fitted_closure: float
    residual: float
    shell_spread: float


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--frame", type=int, default=None)
    parser.add_argument("--frame-limit", type=int, default=None)
    parser.add_argument("--top-k", type=int, default=DEFAULT_TOP_K)
    parser.add_argument("--pool-multiplier", type=int, default=DEFAULT_POOL_MULTIPLIER)
    parser.add_argument("--zero-eps", type=float, default=DEFAULT_ZERO_EPS)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _wrap_phase(angle: float) -> float:
    wrapped = (float(angle) + math.pi) % (2.0 * math.pi) - math.pi
    if wrapped <= -math.pi:
        wrapped += 2.0 * math.pi
    return float(wrapped)


def _fraction(numerator: float, denominator: float) -> float:
    if denominator <= 0.0:
        return 0.0
    return float(numerator) / float(denominator)


def _weighted_quantile(values: np.ndarray, weights: np.ndarray, quantile: float) -> float:
    if len(values) == 0:
        return 0.0
    q = min(max(float(quantile), 0.0), 1.0)
    order = np.argsort(values)
    sorted_values = np.asarray(values[order], dtype=np.float64)
    sorted_weights = np.asarray(weights[order], dtype=np.float64)
    total = float(np.sum(sorted_weights))
    if total <= 0.0 or not math.isfinite(total):
        return float(sorted_values[-1])
    cutoff = q * total
    cumulative = np.cumsum(sorted_weights)
    index = int(np.searchsorted(cumulative, cutoff, side="left"))
    index = max(0, min(index, len(sorted_values) - 1))
    return float(sorted_values[index])


def _weighted_circular_mean(phases: np.ndarray, weights: np.ndarray) -> float:
    total = float(np.sum(weights))
    if total <= 0.0:
        return 0.0
    z = np.sum(np.asarray(weights, dtype=np.float64) * np.exp(1j * np.asarray(phases, dtype=np.float64)))
    if abs(z) <= 0.0:
        return 0.0
    return float(math.atan2(z.imag, z.real))


def _phase_design_matrix(modes: list[ModeRecord]) -> np.ndarray:
    radii = np.asarray([mode.shell_radius for mode in modes], dtype=np.float64)
    return np.column_stack(
        [
            np.ones_like(radii),
            radii,
            radii * radii,
        ]
    )


def _fit_phase_field(modes: list[ModeRecord], zero_eps: float) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, float]:
    if not modes:
        empty = np.zeros(0, dtype=np.float64)
        return empty, empty, empty, empty, 0.0
    amplitudes = np.asarray([max(mode.amplitude, float(zero_eps)) for mode in modes], dtype=np.float64)
    phases = np.asarray([mode.phase for mode in modes], dtype=np.float64)
    basis = _phase_design_matrix(modes)
    reference = _weighted_circular_mean(phases, amplitudes)
    centered = np.asarray([_wrap_phase(phase - reference) for phase in phases], dtype=np.float64)
    targets = np.exp(1j * centered)
    sqrt_w = np.sqrt(amplitudes)
    basis_w = basis * sqrt_w[:, None]
    real_coef = np.linalg.lstsq(basis_w, np.real(targets) * sqrt_w, rcond=None)[0]
    imag_coef = np.linalg.lstsq(basis_w, np.imag(targets) * sqrt_w, rcond=None)[0]
    fitted = (basis @ real_coef) + 1j * (basis @ imag_coef)
    fitted_phase = np.asarray(
        [
            _wrap_phase(math.atan2(value.imag, value.real) + reference)
            if abs(value) > float(zero_eps)
            else reference
            for value in fitted
        ],
        dtype=np.float64,
    )
    phase_residual = np.asarray(
        [_wrap_phase(actual - predicted) for actual, predicted in zip(phases, fitted_phase)],
        dtype=np.float64,
    )
    fit_rmse = float(math.sqrt(np.sum(amplitudes * phase_residual * phase_residual) / max(float(np.sum(amplitudes)), float(zero_eps))))
    return fitted_phase, real_coef, imag_coef, phase_residual, fit_rmse


def _build_resonant_triads(
    modes: list[ModeRecord],
    fitted_phase: np.ndarray,
    zero_eps: float,
) -> list[TriadRecord]:
    if len(modes) < 3:
        return []

    key_to_index = {mode.key: index for index, mode in enumerate(modes)}
    triads: list[TriadRecord] = []
    for left in range(len(modes)):
        mode_left = modes[left]
        for right in range(left, len(modes)):
            mode_right = modes[right]
            key_out = (
                mode_left.key[0] + mode_right.key[0],
                mode_left.key[1] + mode_right.key[1],
                mode_left.key[2] + mode_right.key[2],
            )
            out = key_to_index.get(key_out)
            if out is None or out == left or out == right:
                continue
            mode_out = modes[out]
            weight = mode_left.amplitude * mode_right.amplitude * mode_out.amplitude
            if not math.isfinite(weight) or weight <= float(zero_eps):
                continue
            closure = _wrap_phase(mode_left.phase + mode_right.phase - mode_out.phase)
            fitted_closure = _wrap_phase(fitted_phase[left] + fitted_phase[right] - fitted_phase[out])
            residual = abs(_wrap_phase(closure - fitted_closure))
            shell_spread = max(mode_left.shell_radius, mode_right.shell_radius, mode_out.shell_radius) - min(
                mode_left.shell_radius,
                mode_right.shell_radius,
                mode_out.shell_radius,
            )
            triads.append(
                TriadRecord(
                    left=int(left),
                    right=int(right),
                    out=int(out),
                    weight=float(weight),
                    closure=float(closure),
                    fitted_closure=float(fitted_closure),
                    residual=float(residual),
                    shell_spread=float(shell_spread),
                )
            )
    return triads


def _summarize_triads(triads: list[TriadRecord], modes: list[ModeRecord], phase_fit_rmse: float) -> dict[str, Any]:
    if not triads:
        amplitudes = np.asarray([mode.amplitude for mode in modes], dtype=np.float64)
        amp_sum = float(np.sum(amplitudes))
        mode_concentration = _fraction(float(np.max(amplitudes)) if len(amplitudes) else 0.0, amp_sum)
        return {
            "triad_count": 0,
            "triad_weight_sum": 0.0,
            "triad_weight_mean": 0.0,
            "triad_weight_p95": 0.0,
            "triad_weight_concentration": 0.0,
            "triad_weight_entropy_normalized": 0.0,
            "triad_effective_count": 0.0,
            "triad_phase_coherence": 0.0,
            "coherence_loss_proxy": 1.0,
            "frustration_residual_mean": 0.0,
            "frustration_residual_rmse": 0.0,
            "frustration_residual_p95": 0.0,
            "triad_shell_spread_mean": 0.0,
            "triad_shell_spread_p95": 0.0,
            "mode_concentration_fraction": mode_concentration,
            "phase_field_fit_rmse": float(phase_fit_rmse),
        }

    weights = np.asarray([triad.weight for triad in triads], dtype=np.float64)
    closures = np.asarray([triad.closure for triad in triads], dtype=np.float64)
    fitted = np.asarray([triad.fitted_closure for triad in triads], dtype=np.float64)
    residuals = np.asarray([triad.residual for triad in triads], dtype=np.float64)
    spreads = np.asarray([triad.shell_spread for triad in triads], dtype=np.float64)
    total_weight = float(np.sum(weights))
    normalized = weights / total_weight if total_weight > 0.0 else np.zeros_like(weights)
    concentration = float(np.max(normalized)) if len(normalized) else 0.0
    entropy = float(-np.sum(normalized[normalized > 0.0] * np.log(normalized[normalized > 0.0]))) if total_weight > 0.0 else 0.0
    entropy_norm = entropy / math.log(len(weights)) if len(weights) > 1 else 0.0
    effective_count = float((total_weight * total_weight) / max(float(np.sum(weights * weights)), 1.0e-12))
    phase_coherence = float(abs(np.sum(weights * np.exp(1j * closures))) / max(total_weight, 1.0e-12))
    coherence_loss = float(max(0.0, 1.0 - phase_coherence))
    avg_residual = float(np.sum(weights * residuals) / max(total_weight, 1.0e-12))
    rmse = float(math.sqrt(np.sum(weights * residuals * residuals) / max(total_weight, 1.0e-12)))
    triad_weight_mean = float(np.mean(weights))
    triad_weight_p95 = _weighted_quantile(weights, weights, 0.95)
    resid_p95 = _weighted_quantile(residuals, weights, 0.95)
    spread_p95 = _weighted_quantile(spreads, weights, 0.95)
    mode_amplitudes = np.asarray([mode.amplitude for mode in modes], dtype=np.float64)
    amp_sum = float(np.sum(mode_amplitudes))
    mode_concentration = _fraction(float(np.max(mode_amplitudes)) if len(mode_amplitudes) else 0.0, amp_sum)
    return {
        "triad_count": int(len(triads)),
        "triad_weight_sum": total_weight,
        "triad_weight_mean": triad_weight_mean,
        "triad_weight_p95": float(triad_weight_p95),
        "triad_weight_concentration": concentration,
        "triad_weight_entropy_normalized": float(entropy_norm),
        "triad_effective_count": effective_count,
        "triad_phase_coherence": phase_coherence,
        "coherence_loss_proxy": coherence_loss,
        "frustration_residual_mean": avg_residual,
        "frustration_residual_rmse": rmse,
        "frustration_residual_p95": float(resid_p95),
        "triad_shell_spread_mean": float(np.sum(weights * spreads) / max(total_weight, 1.0e-12)),
        "triad_shell_spread_p95": float(spread_p95),
        "mode_concentration_fraction": mode_concentration,
        "phase_field_fit_rmse": float(phase_fit_rmse),
    }


def _evaluate_frame(
    slot: int,
    snapshot: int,
    bundle: Any,
    top_k: int,
    pool_multiplier: int,
    zero_eps: float,
) -> tuple[str, dict[str, Any]]:
    row: dict[str, Any] = {
        "frame": int(slot),
        "snapshot_index": int(snapshot),
        "orbit_phase": float(snapshot),
        "source": str(bundle.path),
        "top_k": int(top_k),
        "route_mode": "fail-closed",
        "candidate_only": True,
        "empirical_non_promoting": True,
    }
    try:
        u, v, w = _frame_velocity(bundle, snapshot)
        spectrum = _scalar_vorticity_spectrum(u, v, w, bundle.domain_length)
        modes = _collect_modes(
            spectrum,
            top_k=int(top_k),
            zero_eps=float(zero_eps),
            pool_multiplier=int(pool_multiplier),
        )
        fitted_phase, _, _, _, phase_fit_rmse = _fit_phase_field(modes, zero_eps=zero_eps)
        triads = _build_resonant_triads(modes, fitted_phase, zero_eps=zero_eps)
        summary = _summarize_triads(triads, modes, phase_fit_rmse)
    except Exception as exc:  # noqa: BLE001
        row["status"] = ERROR_STATUS
        row["errors"] = [f"frame_triad_frustration_scan_error: {exc}"]
        return ERROR_STATUS, row

    row.update(
        {
            "selected_mode_count": int(len(modes)),
            "selected_mode_amplitude_sum": float(sum(mode.amplitude for mode in modes)),
            "triad_count": int(summary["triad_count"]),
            "triad_weight_sum": float(summary["triad_weight_sum"]),
            "triad_weight_mean": float(summary["triad_weight_mean"]),
            "triad_weight_p95": float(summary["triad_weight_p95"]),
            "triad_weight_concentration": float(summary["triad_weight_concentration"]),
            "triad_weight_entropy_normalized": float(summary["triad_weight_entropy_normalized"]),
            "triad_effective_count": float(summary["triad_effective_count"]),
            "triad_phase_coherence": float(summary["triad_phase_coherence"]),
            "coherence_loss_proxy": float(summary["coherence_loss_proxy"]),
            "frustration_residual_mean": float(summary["frustration_residual_mean"]),
            "frustration_residual_rmse": float(summary["frustration_residual_rmse"]),
            "frustration_residual_p95": float(summary["frustration_residual_p95"]),
            "triad_shell_spread_mean": float(summary["triad_shell_spread_mean"]),
            "triad_shell_spread_p95": float(summary["triad_shell_spread_p95"]),
            "mode_concentration_fraction": float(summary["mode_concentration_fraction"]),
            "phase_field_fit_rmse": float(summary["phase_field_fit_rmse"]),
            "triad_weight_per_mode": _fraction(float(summary["triad_weight_sum"]), float(len(modes))),
            "triad_effective_fraction_of_selected_modes": _fraction(float(summary["triad_effective_count"]), float(len(modes))),
            "frustration_density": _fraction(float(summary["frustration_residual_mean"]), float(summary["triad_weight_sum"])),
        }
    )

    if int(summary["triad_count"]) <= 0:
        row["status"] = PARTIAL_STATUS
        row["warnings"] = ["no resonant selected-mode triads found"]
        return PARTIAL_STATUS, row

    row["status"] = OK_STATUS
    return OK_STATUS, row


def main() -> int:
    args = _parse_args()
    warnings: list[str] = []
    try:
        bundle = _load_raw_bundle(Path(args.raw_archive), warnings)
    except Exception as exc:  # noqa: BLE001
        payload = {
            **CONTROL_CARD,
            "control_card": CONTROL_CARD,
            "contract": CONTRACT,
            "route_decision": ROUTE_DECISION,
            "route_mode": "fail-closed",
            "fail_closed": True,
            "schema_version": SCHEMA_VERSION,
            "script": SCRIPT_NAME,
            "authority": AUTHORITY,
            "status": ERROR_STATUS,
            "errors": [str(exc)],
            "warnings": warnings,
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(payload, args.pretty))
        return 1

    rows: list[dict[str, Any]] = []
    counts = {OK_STATUS: 0, PARTIAL_STATUS: 0, ERROR_STATUS: 0}
    slots = _frame_indices(bundle.frame_count, args.frame, args.frame_limit)
    for slot in slots:
        status, row = _evaluate_frame(
            slot=slot,
            snapshot=slot,
            bundle=bundle,
            top_k=int(args.top_k),
            pool_multiplier=int(args.pool_multiplier),
            zero_eps=float(args.zero_eps),
        )
        counts[status] = counts.get(status, 0) + 1
        rows.append(row)

    ok_rows = [row for row in rows if row.get("status") == OK_STATUS]
    aggregate = {
        "processed_frames": len(rows),
        "ok_frames": counts.get(OK_STATUS, 0),
        "partial_frames": counts.get(PARTIAL_STATUS, 0),
        "error_frames": counts.get(ERROR_STATUS, 0),
        "top_k": int(args.top_k),
        "pool_multiplier": int(args.pool_multiplier),
        "zero_eps": float(args.zero_eps),
        "triad_count_mean": float(np.mean([row.get("triad_count", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "triad_count_total": int(sum(int(row.get("triad_count", 0)) for row in ok_rows)),
        "selected_mode_count_mean": float(np.mean([row.get("selected_mode_count", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "triad_weight_sum_mean": float(np.mean([row.get("triad_weight_sum", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "triad_weight_concentration_mean": float(np.mean([row.get("triad_weight_concentration", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "triad_weight_entropy_normalized_mean": float(np.mean([row.get("triad_weight_entropy_normalized", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "triad_effective_count_mean": float(np.mean([row.get("triad_effective_count", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "triad_phase_coherence_mean": float(np.mean([row.get("triad_phase_coherence", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "coherence_loss_proxy_mean": float(np.mean([row.get("coherence_loss_proxy", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "frustration_residual_mean": float(np.mean([row.get("frustration_residual_mean", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "frustration_residual_rmse_mean": float(np.mean([row.get("frustration_residual_rmse", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "frustration_residual_p95_mean": float(np.mean([row.get("frustration_residual_p95", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "phase_field_fit_rmse_mean": float(np.mean([row.get("phase_field_fit_rmse", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "mode_concentration_fraction_mean": float(np.mean([row.get("mode_concentration_fraction", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "triad_shell_spread_mean": float(np.mean([row.get("triad_shell_spread_mean", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "triad_shell_spread_p95_mean": float(np.mean([row.get("triad_shell_spread_p95", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "triad_weight_per_mode_mean": float(np.mean([row.get("triad_weight_per_mode", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "effective_fraction_of_selected_modes_mean": float(np.mean([row.get("triad_effective_fraction_of_selected_modes", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "frustration_density_mean": float(np.mean([row.get("frustration_density", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "frustration_vs_coherence_loss_correlation": _pearson(
            [float(row.get("frustration_residual_mean", 0.0)) for row in ok_rows],
            [float(row.get("coherence_loss_proxy", 0.0)) for row in ok_rows],
        ),
        "triad_weight_vs_frustration_correlation": _pearson(
            [float(row.get("triad_weight_sum", 0.0)) for row in ok_rows],
            [float(row.get("frustration_residual_mean", 0.0)) for row in ok_rows],
        ),
    }

    payload = {
        **CONTROL_CARD,
        "control_card": CONTROL_CARD,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "route_mode": "fail-closed",
        "fail_closed": True,
        "schema_version": SCHEMA_VERSION,
        "script": SCRIPT_NAME,
        "authority": AUTHORITY,
        "inputs": {
            "raw_archive": str(args.raw_archive),
            "output_json": str(args.output_json),
        },
        "parameters": {
            "top_k": int(args.top_k),
            "pool_multiplier": int(args.pool_multiplier),
            "zero_eps": float(args.zero_eps),
            "frame": args.frame,
            "frame_limit": args.frame_limit,
        },
        "status": OK_STATUS if counts.get(ERROR_STATUS, 0) == 0 and counts.get(PARTIAL_STATUS, 0) == 0 else PARTIAL_STATUS,
        "warnings": warnings,
        "errors": [],
        "aggregate": aggregate,
        "triad_frustration_rows": rows,
    }

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, args.pretty))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
