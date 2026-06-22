#!/usr/bin/env python3
"""Scan triad-derived phase-graph Laplacian proxies on the raw N128 archive.

This is an empirical, candidate-only telemetry scan. It reuses the raw archive
and dominant selected-mode carrier from the existing orbit / frustration scans,
then builds a finite-dimensional triad phase graph and measures unsigned and
signed Laplacian proxies. The output is fail-closed JSON with explicit route
metadata and framewise stability diagnostics.
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


SCRIPT_NAME = "scripts/ns_triad_phase_laplacian_scan.py"
CONTRACT = "ns_triad_phase_laplacian_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_PHASE_LAPLACIAN_SCAN"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"

DEFAULT_RAW_ARCHIVE = Path(
    "/home/c/Documents/code/dashiCFD/outputs/"
    "sprint65_pressure_reconstruction_N128_seed0_gpu/ns3d_N128_seed0_gpu_pressure.npz"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_phase_laplacian_scan_N128_20260621.json"
)
DEFAULT_TOP_K = 48
DEFAULT_POOL_MULTIPLIER = 24
DEFAULT_ZERO_EPS = 1.0e-12
DEFAULT_EIGEN_TOL = 1.0e-10

CONTROL_CARD = {
    "O": "Measure candidate triad phase-graph Laplacian telemetry on the raw N128 archive.",
    "R": (
        "Build a finite-dimensional phase graph from resonant selected-mode triads, then "
        "summarize unsigned and signed Laplacian proxies together with negative-frame stability metrics."
    ),
    "C": SCRIPT_NAME,
    "S": "Telemetry only; the phase-graph carrier is empirical and non-promoting.",
    "L": (
        "Load raw frames, select dominant modes, form resonant triads, assemble Laplacian proxies, "
        "and emit framewise plus aggregate stability diagnostics."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, Clay, or route promotion is inferred from this scan.",
    "F": "The finite carrier may expose stability structure, but it does not prove any operator bound.",
}


@dataclass(frozen=True)
class TriadSurfaceRecord:
    left: int
    right: int
    out: int
    weight: float
    closure: float
    coherence: float
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


def _smallest_positive_eigenvalue(eigenvalues: np.ndarray, tol: float) -> float:
    positives = np.asarray([float(value) for value in eigenvalues if float(value) > float(tol)], dtype=np.float64)
    if len(positives) == 0:
        return 0.0
    return float(np.min(positives))


def _laplacian_from_adjacency(adjacency: np.ndarray, signed: bool) -> np.ndarray:
    if adjacency.size == 0:
        return np.zeros_like(adjacency, dtype=np.float64)
    if signed:
        degree = np.sum(np.abs(adjacency), axis=1)
    else:
        degree = np.sum(adjacency, axis=1)
    return np.diag(degree) - adjacency


def _build_phase_surface(modes: list[ModeRecord], zero_eps: float) -> tuple[list[TriadSurfaceRecord], dict[str, Any]]:
    if len(modes) < 3:
        amp_sum = float(np.sum([mode.amplitude for mode in modes], dtype=np.float64)) if modes else 0.0
        mode_concentration = _fraction(float(max([mode.amplitude for mode in modes], default=0.0)), amp_sum)
        shell_radius_mean = float(np.mean([mode.shell_radius for mode in modes])) if modes else 0.0
        return [], {
            "triad_count": 0,
            "triad_weight_sum": 0.0,
            "triad_weight_mean": 0.0,
            "triad_weight_p95": 0.0,
            "triad_shell_spread_mean": 0.0,
            "triad_shell_spread_p95": 0.0,
            "triad_phase_alignment_mean": 0.0,
            "triad_phase_alignment_abs_mean": 0.0,
            "triad_negative_mass": 0.0,
            "triad_positive_mass": 0.0,
            "triad_negative_mass_ratio": 0.0,
            "selected_mode_count": len(modes),
            "selected_mode_amplitude_sum": amp_sum,
            "mode_concentration_fraction": mode_concentration,
            "shell_radius_mean": shell_radius_mean,
            "phase_graph_unsigned_laplacian_trace": 0.0,
            "phase_graph_unsigned_laplacian_spectral_gap_proxy": 0.0,
            "phase_graph_unsigned_laplacian_zero_eigen_count": 0,
            "phase_graph_signed_laplacian_trace": 0.0,
            "phase_graph_signed_smallest_positive_eigenvalue_proxy": 0.0,
            "phase_graph_signed_laplacian_zero_eigen_count": 0,
            "phase_graph_subunit_proxy": 0.0,
            "phase_graph_stability_margin_proxy": 0.0,
        }

    key_to_index = {mode.key: idx for idx, mode in enumerate(modes)}
    triads: list[TriadSurfaceRecord] = []
    unsigned_adjacency = np.zeros((len(modes), len(modes)), dtype=np.float64)
    signed_adjacency = np.zeros_like(unsigned_adjacency)

    total_weight = 0.0
    triad_weight_values: list[float] = []
    shell_spreads: list[float] = []
    alignment_values: list[float] = []
    alignment_abs_values: list[float] = []
    negative_mass = 0.0
    positive_mass = 0.0

    for left in range(len(modes)):
        mode_left = modes[left]
        for right in range(left + 1, len(modes)):
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
            coherence = float(math.cos(closure))
            pair_weight = float(weight) / 3.0
            signed_pair_weight = pair_weight * coherence
            for a, b in ((left, right), (left, out), (right, out)):
                unsigned_adjacency[a, b] += pair_weight
                unsigned_adjacency[b, a] += pair_weight
                signed_adjacency[a, b] += signed_pair_weight
                signed_adjacency[b, a] += signed_pair_weight

            spread = max(mode_left.shell_radius, mode_right.shell_radius, mode_out.shell_radius) - min(
                mode_left.shell_radius,
                mode_right.shell_radius,
                mode_out.shell_radius,
            )
            triads.append(
                TriadSurfaceRecord(
                    left=int(left),
                    right=int(right),
                    out=int(out),
                    weight=float(weight),
                    closure=float(closure),
                    coherence=float(coherence),
                    shell_spread=float(spread),
                )
            )
            total_weight += float(weight)
            triad_weight_values.append(float(weight))
            shell_spreads.append(float(spread))
            alignment_values.append(float(weight) * coherence)
            alignment_abs_values.append(float(weight) * abs(coherence))
            if coherence < 0.0:
                negative_mass += float(weight) * abs(coherence)
            else:
                positive_mass += float(weight) * coherence

    triad_count = len(triads)
    amplitudes = np.asarray([mode.amplitude for mode in modes], dtype=np.float64)
    amp_sum = float(np.sum(amplitudes))
    mode_concentration = _fraction(float(np.max(amplitudes)) if len(amplitudes) else 0.0, amp_sum)
    shell_radius_mean = float(np.mean([mode.shell_radius for mode in modes]))

    if triad_count == 0 or total_weight <= float(zero_eps):
        return triads, {
            "triad_count": 0,
            "triad_weight_sum": 0.0,
            "triad_weight_mean": 0.0,
            "triad_weight_p95": 0.0,
            "triad_shell_spread_mean": 0.0,
            "triad_shell_spread_p95": 0.0,
            "triad_phase_alignment_mean": 0.0,
            "triad_phase_alignment_abs_mean": 0.0,
            "triad_negative_mass": 0.0,
            "triad_positive_mass": 0.0,
            "triad_negative_mass_ratio": 0.0,
            "selected_mode_count": len(modes),
            "selected_mode_amplitude_sum": amp_sum,
            "mode_concentration_fraction": mode_concentration,
            "shell_radius_mean": shell_radius_mean,
            "phase_graph_unsigned_laplacian_trace": 0.0,
            "phase_graph_unsigned_laplacian_spectral_gap_proxy": 0.0,
            "phase_graph_unsigned_laplacian_zero_eigen_count": 0,
            "phase_graph_signed_laplacian_trace": 0.0,
            "phase_graph_signed_smallest_positive_eigenvalue_proxy": 0.0,
            "phase_graph_signed_laplacian_zero_eigen_count": 0,
            "phase_graph_subunit_proxy": 0.0,
            "phase_graph_stability_margin_proxy": 0.0,
        }

    unsigned_laplacian = _laplacian_from_adjacency(unsigned_adjacency, signed=False)
    signed_laplacian = _laplacian_from_adjacency(signed_adjacency, signed=True)
    unsigned_eigenvalues = np.linalg.eigvalsh(unsigned_laplacian) if len(modes) > 1 else np.zeros(1, dtype=np.float64)
    signed_eigenvalues = np.linalg.eigvalsh(signed_laplacian) if len(modes) > 1 else np.zeros(1, dtype=np.float64)
    eigen_tol = max(float(DEFAULT_EIGEN_TOL), float(zero_eps) * 100.0)
    unsigned_gap = _smallest_positive_eigenvalue(unsigned_eigenvalues, eigen_tol)
    signed_gap = _smallest_positive_eigenvalue(signed_eigenvalues, eigen_tol)
    unsigned_zero_count = int(np.sum(np.abs(unsigned_eigenvalues) <= eigen_tol))
    signed_zero_count = int(np.sum(np.abs(signed_eigenvalues) <= eigen_tol))
    unsigned_trace = float(np.trace(unsigned_laplacian))
    signed_trace = float(np.trace(signed_laplacian))
    negative_mass_ratio = _fraction(negative_mass, total_weight)
    phase_alignment_mean = _fraction(float(np.sum(alignment_values)), total_weight)
    phase_alignment_abs_mean = _fraction(float(np.sum(alignment_abs_values)), total_weight)
    triad_weight_mean = float(np.mean(np.asarray(triad_weight_values, dtype=np.float64)))
    triad_weight_p95 = _weighted_quantile(
        np.asarray(triad_weight_values, dtype=np.float64),
        np.asarray(triad_weight_values, dtype=np.float64),
        0.95,
    )
    shell_spread_mean = float(np.mean(np.asarray(shell_spreads, dtype=np.float64)))
    shell_spread_p95 = _weighted_quantile(
        np.asarray(shell_spreads, dtype=np.float64),
        np.asarray(triad_weight_values, dtype=np.float64),
        0.95,
    )
    subunit_proxy = _fraction(signed_gap, 1.0 + signed_trace)
    stability_margin_proxy = max(0.0, _fraction(unsigned_gap, 1.0 + unsigned_trace) * max(0.0, 1.0 - negative_mass_ratio))

    return triads, {
        "triad_count": int(triad_count),
        "triad_weight_sum": float(total_weight),
        "triad_weight_mean": float(triad_weight_mean),
        "triad_weight_p95": float(triad_weight_p95),
        "triad_shell_spread_mean": float(shell_spread_mean),
        "triad_shell_spread_p95": float(shell_spread_p95),
        "triad_phase_alignment_mean": float(phase_alignment_mean),
        "triad_phase_alignment_abs_mean": float(phase_alignment_abs_mean),
        "triad_negative_mass": float(negative_mass),
        "triad_positive_mass": float(positive_mass),
        "triad_negative_mass_ratio": float(negative_mass_ratio),
        "selected_mode_count": len(modes),
        "selected_mode_amplitude_sum": float(amp_sum),
        "mode_concentration_fraction": float(mode_concentration),
        "shell_radius_mean": float(shell_radius_mean),
        "phase_graph_unsigned_laplacian_trace": float(unsigned_trace),
        "phase_graph_unsigned_laplacian_spectral_gap_proxy": float(unsigned_gap),
        "phase_graph_unsigned_laplacian_zero_eigen_count": int(unsigned_zero_count),
        "phase_graph_signed_laplacian_trace": float(signed_trace),
        "phase_graph_signed_smallest_positive_eigenvalue_proxy": float(signed_gap),
        "phase_graph_signed_laplacian_zero_eigen_count": int(signed_zero_count),
        "phase_graph_subunit_proxy": float(subunit_proxy),
        "phase_graph_stability_margin_proxy": float(stability_margin_proxy),
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
        "source": str(bundle.path),
        "orbit_phase": float(snapshot),
        "top_k": int(top_k),
        "route_mode": "fail-closed",
        "fail_closed": True,
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
        _triads, metrics = _build_phase_surface(modes, zero_eps=zero_eps)
    except Exception as exc:  # noqa: BLE001
        row["status"] = ERROR_STATUS
        row["errors"] = [f"frame_triad_phase_laplacian_scan_error: {exc}"]
        return ERROR_STATUS, row

    row.update(
        {
            "selected_mode_count": int(metrics["selected_mode_count"]),
            "selected_mode_amplitude_sum": float(metrics["selected_mode_amplitude_sum"]),
            "triad_count": int(metrics["triad_count"]),
            "triad_weight_sum": float(metrics["triad_weight_sum"]),
            "triad_weight_mean": float(metrics["triad_weight_mean"]),
            "triad_weight_p95": float(metrics["triad_weight_p95"]),
            "triad_shell_spread_mean": float(metrics["triad_shell_spread_mean"]),
            "triad_shell_spread_p95": float(metrics["triad_shell_spread_p95"]),
            "triad_phase_alignment_mean": float(metrics["triad_phase_alignment_mean"]),
            "triad_phase_alignment_abs_mean": float(metrics["triad_phase_alignment_abs_mean"]),
            "triad_negative_mass": float(metrics["triad_negative_mass"]),
            "triad_positive_mass": float(metrics["triad_positive_mass"]),
            "triad_negative_mass_ratio": float(metrics["triad_negative_mass_ratio"]),
            "mode_concentration_fraction": float(metrics["mode_concentration_fraction"]),
            "shell_radius_mean": float(metrics["shell_radius_mean"]),
            "phase_graph_unsigned_laplacian_trace": float(metrics["phase_graph_unsigned_laplacian_trace"]),
            "phase_graph_unsigned_laplacian_spectral_gap_proxy": float(
                metrics["phase_graph_unsigned_laplacian_spectral_gap_proxy"]
            ),
            "phase_graph_unsigned_laplacian_zero_eigen_count": int(
                metrics["phase_graph_unsigned_laplacian_zero_eigen_count"]
            ),
            "phase_graph_signed_laplacian_trace": float(metrics["phase_graph_signed_laplacian_trace"]),
            "phase_graph_signed_smallest_positive_eigenvalue_proxy": float(
                metrics["phase_graph_signed_smallest_positive_eigenvalue_proxy"]
            ),
            "phase_graph_signed_laplacian_zero_eigen_count": int(
                metrics["phase_graph_signed_laplacian_zero_eigen_count"]
            ),
            "phase_graph_subunit_proxy": float(metrics["phase_graph_subunit_proxy"]),
            "phase_graph_stability_margin_proxy": float(metrics["phase_graph_stability_margin_proxy"]),
        }
    )

    warnings: list[str] = []
    if int(metrics["triad_count"]) <= 0:
        warnings.append("no resonant selected-mode triads found")
    if float(metrics["phase_graph_unsigned_laplacian_spectral_gap_proxy"]) <= 0.0:
        warnings.append("unsigned phase-graph laplacian is singular or disconnected")
    if float(metrics["phase_graph_signed_smallest_positive_eigenvalue_proxy"]) <= 0.0:
        warnings.append("signed phase-graph laplacian has no positive eigenvalue proxy")
    if warnings:
        row["status"] = PARTIAL_STATUS
        row["warnings"] = warnings
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
            "triad_phase_laplacian_rows": [],
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(payload, args.pretty))
        return 1

    slots = _frame_indices(bundle.frame_count, args.frame, args.frame_limit)
    if not slots:
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
            "errors": ["no frames selected for triad phase Laplacian scan"],
            "warnings": warnings,
            "triad_phase_laplacian_rows": [],
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(payload, args.pretty))
        return 1

    rows: list[dict[str, Any]] = []
    counts = {OK_STATUS: 0, PARTIAL_STATUS: 0, ERROR_STATUS: 0}
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
        "selected_mode_count_mean": float(np.mean([row.get("selected_mode_count", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "selected_mode_amplitude_sum_mean": float(np.mean([row.get("selected_mode_amplitude_sum", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "triad_count_mean": float(np.mean([row.get("triad_count", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "triad_count_total": int(sum(int(row.get("triad_count", 0)) for row in ok_rows)),
        "triad_weight_sum_mean": float(np.mean([row.get("triad_weight_sum", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "triad_phase_alignment_mean": float(np.mean([row.get("triad_phase_alignment_mean", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "triad_negative_mass_ratio_mean": float(np.mean([row.get("triad_negative_mass_ratio", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "phase_graph_unsigned_laplacian_trace_mean": float(
            np.mean([row.get("phase_graph_unsigned_laplacian_trace", 0.0) for row in ok_rows])
        ) if ok_rows else 0.0,
        "phase_graph_unsigned_laplacian_spectral_gap_proxy_mean": float(
            np.mean([row.get("phase_graph_unsigned_laplacian_spectral_gap_proxy", 0.0) for row in ok_rows])
        ) if ok_rows else 0.0,
        "phase_graph_signed_smallest_positive_eigenvalue_proxy_mean": float(
            np.mean([row.get("phase_graph_signed_smallest_positive_eigenvalue_proxy", 0.0) for row in ok_rows])
        ) if ok_rows else 0.0,
        "phase_graph_negative_mass_ratio_mean": float(
            np.mean([row.get("triad_negative_mass_ratio", 0.0) for row in ok_rows])
        ) if ok_rows else 0.0,
        "phase_graph_subunit_proxy_mean": float(np.mean([row.get("phase_graph_subunit_proxy", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "phase_graph_stability_margin_proxy_mean": float(
            np.mean([row.get("phase_graph_stability_margin_proxy", 0.0) for row in ok_rows])
        ) if ok_rows else 0.0,
        "phase_graph_negative_mass_ratio_vs_gap_correlation": _pearson(
            [float(row.get("triad_negative_mass_ratio", 0.0)) for row in ok_rows],
            [float(row.get("phase_graph_unsigned_laplacian_spectral_gap_proxy", 0.0)) for row in ok_rows],
        ),
        "phase_graph_negative_mass_ratio_vs_stability_correlation": _pearson(
            [float(row.get("triad_negative_mass_ratio", 0.0)) for row in ok_rows],
            [float(row.get("phase_graph_stability_margin_proxy", 0.0)) for row in ok_rows],
        ),
        "triad_count_vs_gap_correlation": _pearson(
            [float(row.get("triad_count", 0.0)) for row in ok_rows],
            [float(row.get("phase_graph_unsigned_laplacian_spectral_gap_proxy", 0.0)) for row in ok_rows],
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
        "triad_phase_laplacian_rows": rows,
    }

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, args.pretty))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
