#!/usr/bin/env python3
"""Scan resonant-triad cycle obstruction telemetry on the raw N128 archive.

This producer is empirical and candidate-only. It reuses the existing
selected-mode carrier from the orbit / incidence scans, builds resonant triads
from the dominant Fourier-vorticity modes, and measures cycle-rank and cocycle
residue style telemetry on the induced triad graph.

The output is deliberately fail-closed: missing archive data, malformed frame
selection, or non-finite arithmetic are emitted as explicit errors rather than
silently promoted.
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


SCRIPT_NAME = "scripts/ns_triad_cycle_obstruction_scan.py"
CONTRACT = "ns_triad_cycle_obstruction_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_CYCLE_OBSTRUCTION_SCAN"
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
    "ns_triad_cycle_obstruction_scan_N128_20260621.json"
)
DEFAULT_TOP_K = 48
DEFAULT_POOL_MULTIPLIER = 24
DEFAULT_ZERO_EPS = 1.0e-12
DEFAULT_LOCK_EPS = 1.0e-6

CONTROL_CARD = {
    "O": "Measure candidate resonant-triad cycle obstruction telemetry on the raw N128 archive.",
    "R": (
        "Build a fail-closed triad carrier from dominant Fourier-vorticity modes, "
        "then summarize cycle-rank proxies and cocycle residue telemetry on the induced triad graph."
    ),
    "C": SCRIPT_NAME,
    "S": "Telemetry only; the cycle-obstruction carrier is empirical and non-promoting.",
    "L": (
        "Load raw frames, select dominant modes, form resonant selected-mode triads, "
        "and emit framewise cycle-obstruction metrics."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, Clay, or route promotion is inferred from this scan.",
    "F": "A low cycle-rank proxy or low cocycle residue is still only empirical telemetry, not a proof."
}


@dataclass(frozen=True)
class TriadCycleRecord:
    mode_indices: list[int]
    mode_keys: list[list[int]]
    incidence_signs: list[int]
    weight: float
    phase_mismatch: float
    abs_phase_mismatch: float
    exact_lock_hit: bool

    def as_row(self) -> dict[str, Any]:
        return {
            "mode_indices": self.mode_indices,
            "mode_keys": self.mode_keys,
            "incidence_signs": self.incidence_signs,
            "weight": self.weight,
            "phase_mismatch": self.phase_mismatch,
            "abs_phase_mismatch": self.abs_phase_mismatch,
            "exact_lock_hit": self.exact_lock_hit,
        }


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--frame", type=int, default=None)
    parser.add_argument("--frame-limit", type=int, default=None)
    parser.add_argument("--top-k", type=int, default=DEFAULT_TOP_K)
    parser.add_argument("--pool-multiplier", type=int, default=DEFAULT_POOL_MULTIPLIER)
    parser.add_argument("--zero-eps", type=float, default=DEFAULT_ZERO_EPS)
    parser.add_argument("--lock-eps", type=float, default=DEFAULT_LOCK_EPS)
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


def _dominant_mode(mode_records: list[ModeRecord]) -> ModeRecord | None:
    if not mode_records:
        return None
    return max(mode_records, key=lambda mode: mode.amplitude)


def _mode_key_list(modes: list[ModeRecord]) -> list[list[int]]:
    return [list(mode.key) for mode in modes]


def _union_find(nodes: list[int]) -> tuple[dict[int, int], dict[int, int], Any, Any]:
    parent = {node: node for node in nodes}
    rank = {node: 0 for node in nodes}

    def find(node: int) -> int:
        root = node
        while parent[root] != root:
            root = parent[root]
        while parent[node] != node:
            next_node = parent[node]
            parent[node] = root
            node = next_node
        return root

    def union(left: int, right: int) -> None:
        root_left = find(left)
        root_right = find(right)
        if root_left == root_right:
            return
        if rank[root_left] < rank[root_right]:
            parent[root_left] = root_right
        elif rank[root_left] > rank[root_right]:
            parent[root_right] = root_left
        else:
            parent[root_right] = root_left
            rank[root_left] += 1

    return parent, rank, find, union


def _triad_cycle_payload(
    modes: list[ModeRecord],
    zero_eps: float,
    lock_eps: float,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    if len(modes) < 3:
        amplitudes = np.asarray([mode.amplitude for mode in modes], dtype=np.float64)
        amp_sum = float(np.sum(amplitudes))
        mode_concentration = _fraction(float(np.max(amplitudes)) if len(amplitudes) else 0.0, amp_sum)
        shell_radius_mean = float(np.mean([mode.shell_radius for mode in modes])) if modes else 0.0
        return [], {
            "triad_count": 0,
            "triad_weight_sum": 0.0,
            "triad_weight_mean": 0.0,
            "triad_weight_p95": 0.0,
            "triad_weight_concentration": 0.0,
            "triad_weight_entropy_normalized": 0.0,
            "triad_effective_count": 0.0,
            "incidence_nonzero_count": 0,
            "incidence_density": 0.0,
            "mode_graph_edge_count": 0,
            "mode_graph_component_count": len(modes),
            "cycle_rank_proxy": 0,
            "cycle_basis_proxy": 0.0,
            "cycle_obstruction_density": 0.0,
            "cycle_obstruction_score": 0.0,
            "cocycle_residue_mean": 0.0,
            "cocycle_residue_rms": 0.0,
            "cocycle_residue_p95": 0.0,
            "cocycle_residue_max": 0.0,
            "cocycle_exact_lock_fraction": 0.0,
            "exact_lock_residual_rms": 0.0,
            "exact_lock_residual_max": 0.0,
            "exact_lock_near_lock_fraction": 0.0,
            "exact_lock_score": 0.0,
            "mode_concentration_fraction": mode_concentration,
            "carrier_shell_radius_mean": shell_radius_mean,
            "triad_shell_spread_mean": 0.0,
            "triad_shell_spread_p95": 0.0,
        }

    key_to_index = {mode.key: idx for idx, mode in enumerate(modes)}
    triad_records: list[dict[str, Any]] = []
    edge_pairs: set[tuple[int, int]] = set()
    node_indices = list(range(len(modes)))
    _, _, find, union = _union_find(node_indices)

    amplitudes = np.asarray([mode.amplitude for mode in modes], dtype=np.float64)
    phases = np.asarray([mode.phase for mode in modes], dtype=np.float64)
    amp_sum = float(np.sum(amplitudes))
    mode_concentration_fraction = (
        float(np.max(amplitudes)) / amp_sum if amp_sum > float(zero_eps) else 0.0
    )
    carrier_shell_radius_mean = float(np.mean([mode.shell_radius for mode in modes]))

    total_weight = 0.0
    weighted_residual_sq = 0.0
    weighted_abs_residual = 0.0
    max_residual = 0.0
    near_lock_weight = 0.0
    triad_shell_spread_total = 0.0
    triad_weight_values: list[float] = []
    residual_values: list[float] = []
    triad_shell_spread_values: list[float] = []

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

            residual = _wrap_phase(mode_left.phase + mode_right.phase - mode_out.phase)
            abs_residual = abs(residual)
            triad_records.append(
                TriadCycleRecord(
                    mode_indices=[int(left), int(right), int(out)],
                    mode_keys=[list(mode_left.key), list(mode_right.key), list(mode_out.key)],
                    incidence_signs=[1, 1, -1],
                    weight=float(weight),
                    phase_mismatch=float(residual),
                    abs_phase_mismatch=float(abs_residual),
                    exact_lock_hit=bool(abs_residual <= float(lock_eps)),
                ).as_row()
            )

            total_weight += float(weight)
            weighted_residual_sq += float(weight) * float(residual * residual)
            weighted_abs_residual += float(weight) * float(abs_residual)
            max_residual = max(max_residual, abs_residual)
            if abs_residual <= float(lock_eps):
                near_lock_weight += float(weight)
            triad_weight_values.append(float(weight))
            residual_values.append(float(abs_residual))
            triad_shell_spread = max(mode_left.shell_radius, mode_right.shell_radius, mode_out.shell_radius) - min(
                mode_left.shell_radius,
                mode_right.shell_radius,
                mode_out.shell_radius,
            )
            triad_shell_spread_total += float(triad_shell_spread)
            triad_shell_spread_values.append(float(triad_shell_spread))

            for a, b in ((left, right), (left, out), (right, out)):
                edge = (a, b) if a < b else (b, a)
                edge_pairs.add(edge)
                union(a, b)

    triad_count = len(triad_records)
    if triad_count == 0:
        return [], {
            "triad_count": 0,
            "triad_weight_sum": 0.0,
            "triad_weight_mean": 0.0,
            "triad_weight_p95": 0.0,
            "triad_weight_concentration": 0.0,
            "triad_weight_entropy_normalized": 0.0,
            "triad_effective_count": 0.0,
            "incidence_nonzero_count": 0,
            "incidence_density": 0.0,
            "mode_graph_edge_count": len(edge_pairs),
            "mode_graph_component_count": len({find(node) for node in node_indices}),
            "cycle_rank_proxy": 0,
            "cycle_basis_proxy": 0.0,
            "cycle_obstruction_density": 0.0,
            "cycle_obstruction_score": 0.0,
            "cocycle_residue_mean": 0.0,
            "cocycle_residue_rms": 0.0,
            "cocycle_residue_p95": 0.0,
            "cocycle_residue_max": 0.0,
            "cocycle_exact_lock_fraction": 0.0,
            "exact_lock_residual_rms": 0.0,
            "exact_lock_residual_max": 0.0,
            "exact_lock_near_lock_fraction": 0.0,
            "exact_lock_score": 0.0,
            "mode_concentration_fraction": mode_concentration_fraction,
            "carrier_shell_radius_mean": carrier_shell_radius_mean,
            "triad_shell_spread_mean": 0.0,
            "triad_shell_spread_p95": 0.0,
        }

    incidence_nonzero_count = 3 * triad_count
    incidence_density = float(incidence_nonzero_count) / float(len(modes) * triad_count)
    edge_count = len(edge_pairs)
    component_count = len({find(node) for node in node_indices})
    cycle_rank_proxy = max(edge_count - len(modes) + component_count, 0)
    cycle_basis_proxy = float(cycle_rank_proxy) / float(edge_count) if edge_count > 0 else 0.0
    cycle_obstruction_density = _fraction(float(cycle_rank_proxy), float(len(modes)))
    if total_weight > float(zero_eps):
        exact_lock_residual_rms = math.sqrt(weighted_residual_sq / total_weight)
        exact_lock_near_lock_fraction = near_lock_weight / total_weight
        cocycle_residue_mean = weighted_abs_residual / total_weight
    else:
        exact_lock_residual_rms = 0.0
        exact_lock_near_lock_fraction = 0.0
        cocycle_residue_mean = 0.0
    exact_lock_score = 1.0 / (1.0 + exact_lock_residual_rms)
    cocycle_residue_rms = exact_lock_residual_rms
    cocycle_residue_p95 = _weighted_quantile(
        np.asarray(residual_values, dtype=np.float64),
        np.asarray(triad_weight_values, dtype=np.float64),
        0.95,
    )
    cycle_obstruction_score = float(cycle_rank_proxy) * float(cocycle_residue_rms)
    triad_weight_array = np.asarray(triad_weight_values, dtype=np.float64)
    total_weight_sum = float(np.sum(triad_weight_array))
    normalized = triad_weight_array / total_weight_sum if total_weight_sum > 0.0 else np.zeros_like(triad_weight_array)
    entropy = float(-np.sum(normalized[normalized > 0.0] * np.log(normalized[normalized > 0.0]))) if total_weight_sum > 0.0 else 0.0
    entropy_norm = entropy / math.log(len(triad_weight_array)) if len(triad_weight_array) > 1 else 0.0
    effective_count = float((total_weight_sum * total_weight_sum) / max(float(np.sum(triad_weight_array * triad_weight_array)), 1.0e-12))
    triad_weight_mean = float(np.mean(triad_weight_array))
    triad_weight_p95 = _weighted_quantile(triad_weight_array, triad_weight_array, 0.95)
    triad_weight_concentration = float(np.max(normalized)) if len(normalized) else 0.0
    triad_shell_spread_mean = float(triad_shell_spread_total / float(triad_count))
    triad_shell_spread_p95 = _weighted_quantile(
        np.asarray(triad_shell_spread_values, dtype=np.float64),
        triad_weight_array,
        0.95,
    )

    metrics = {
        "triad_count": int(triad_count),
        "triad_weight_sum": float(total_weight_sum),
        "triad_weight_mean": triad_weight_mean,
        "triad_weight_p95": float(triad_weight_p95),
        "triad_weight_concentration": float(triad_weight_concentration),
        "triad_weight_entropy_normalized": float(entropy_norm),
        "triad_effective_count": float(effective_count),
        "incidence_nonzero_count": int(incidence_nonzero_count),
        "incidence_density": float(incidence_density),
        "mode_graph_edge_count": int(edge_count),
        "mode_graph_component_count": int(component_count),
        "cycle_rank_proxy": int(cycle_rank_proxy),
        "cycle_basis_proxy": float(cycle_basis_proxy),
        "cycle_obstruction_density": float(cycle_obstruction_density),
        "cycle_obstruction_score": float(cycle_obstruction_score),
        "cocycle_residue_mean": float(cocycle_residue_mean),
        "cocycle_residue_rms": float(cocycle_residue_rms),
        "cocycle_residue_p95": float(cocycle_residue_p95),
        "cocycle_residue_max": float(max_residual),
        "cocycle_exact_lock_fraction": float(exact_lock_near_lock_fraction),
        "exact_lock_residual_rms": float(exact_lock_residual_rms),
        "exact_lock_residual_max": float(max_residual),
        "exact_lock_near_lock_fraction": float(exact_lock_near_lock_fraction),
        "exact_lock_score": float(exact_lock_score),
        "mode_concentration_fraction": float(mode_concentration_fraction),
        "carrier_shell_radius_mean": float(carrier_shell_radius_mean),
        "triad_shell_spread_mean": float(triad_shell_spread_mean),
        "triad_shell_spread_p95": float(triad_shell_spread_p95),
    }
    return triad_records, metrics


def _evaluate_frame(
    slot: int,
    snapshot: int,
    bundle: Any,
    top_k: int,
    pool_multiplier: int,
    zero_eps: float,
    lock_eps: float,
) -> tuple[str, dict[str, Any]]:
    row: dict[str, Any] = {
        "frame": int(slot),
        "snapshot_index": int(snapshot),
        "source": str(bundle.path),
        "orbit_phase": float(snapshot),
        "top_k": int(top_k),
        "route_mode": "fail-closed",
        "candidate_only": True,
        "empirical_non_promoting": True,
    }
    try:
        u, v, w = _frame_velocity(bundle, snapshot)
        spectrum = _scalar_vorticity_spectrum(u, v, w, bundle.domain_length)
        carrier_modes = _collect_modes(
            spectrum,
            top_k=int(top_k),
            zero_eps=float(zero_eps),
            pool_multiplier=int(pool_multiplier),
        )
        dominant = _dominant_mode(carrier_modes)
        triad_records, metrics = _triad_cycle_payload(
            carrier_modes,
            zero_eps=float(zero_eps),
            lock_eps=float(lock_eps),
        )
    except Exception as exc:  # noqa: BLE001
        row["status"] = ERROR_STATUS
        row["errors"] = [f"frame_triad_cycle_obstruction_scan_error: {exc}"]
        return ERROR_STATUS, row

    if dominant is None:
        row.update(
            {
                "mode_count": 0,
                "carrier_mode_count": 0,
                "selected_mode_count": 0,
                "selected_mode_amplitude_sum": 0.0,
                "dominant_mode_key": None,
                "dominant_mode_amplitude": 0.0,
                "dominant_mode_phase": 0.0,
                "dominant_mode_shell_radius": 0.0,
                "selected_mode_keys": [],
                "triad_cycle_records": [],
                **metrics,
            }
        )
        row["status"] = PARTIAL_STATUS
        row["warnings"] = ["no carrier modes available after dominant-mode filtering"]
        return PARTIAL_STATUS, row

    row.update(
        {
            "mode_count": int(len(carrier_modes)),
            "carrier_mode_count": int(len(carrier_modes)),
            "selected_mode_count": int(len(carrier_modes)),
            "selected_mode_amplitude_sum": float(sum(mode.amplitude for mode in carrier_modes)),
            "dominant_mode_key": list(dominant.key),
            "dominant_mode_amplitude": float(dominant.amplitude),
            "dominant_mode_phase": float(dominant.phase),
            "dominant_mode_shell_radius": float(dominant.shell_radius),
            "selected_mode_keys": _mode_key_list(carrier_modes),
            "triad_cycle_records": triad_records,
            **metrics,
        }
    )

    if int(metrics["triad_count"]) <= 0:
        row["status"] = PARTIAL_STATUS
        row["warnings"] = ["no resonant triads found for selected carrier modes"]
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
            "schema_version": SCHEMA_VERSION,
            "script": SCRIPT_NAME,
            "authority": AUTHORITY,
            "status": ERROR_STATUS,
            "errors": [str(exc)],
            "warnings": warnings,
            "triad_cycle_obstruction_rows": [],
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
            "schema_version": SCHEMA_VERSION,
            "script": SCRIPT_NAME,
            "authority": AUTHORITY,
            "status": ERROR_STATUS,
            "errors": ["no frames selected for triad cycle obstruction scan"],
            "warnings": warnings,
            "triad_cycle_obstruction_rows": [],
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
            lock_eps=float(args.lock_eps),
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
        "lock_eps": float(args.lock_eps),
        "selected_mode_count_mean": float(np.mean([row.get("selected_mode_count", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "triad_count_mean": float(np.mean([row.get("triad_count", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "triad_weight_sum_mean": float(np.mean([row.get("triad_weight_sum", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "incidence_density_mean": float(np.mean([row.get("incidence_density", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "cycle_rank_proxy_mean": float(np.mean([row.get("cycle_rank_proxy", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "cycle_basis_proxy_mean": float(np.mean([row.get("cycle_basis_proxy", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "cycle_obstruction_density_mean": float(np.mean([row.get("cycle_obstruction_density", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "cycle_obstruction_score_mean": float(np.mean([row.get("cycle_obstruction_score", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "cocycle_residue_mean_mean": float(np.mean([row.get("cocycle_residue_mean", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "cocycle_residue_rms_mean": float(np.mean([row.get("cocycle_residue_rms", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "cocycle_residue_p95_mean": float(np.mean([row.get("cocycle_residue_p95", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "cocycle_residue_max_mean": float(np.mean([row.get("cocycle_residue_max", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "exact_lock_score_mean": float(np.mean([row.get("exact_lock_score", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "exact_lock_residual_rms_mean": float(np.mean([row.get("exact_lock_residual_rms", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "exact_lock_residual_max_mean": float(np.mean([row.get("exact_lock_residual_max", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "mode_concentration_fraction_mean": float(np.mean([row.get("mode_concentration_fraction", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "triad_shell_spread_mean_mean": float(np.mean([row.get("triad_shell_spread_mean", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "triad_shell_spread_p95_mean": float(np.mean([row.get("triad_shell_spread_p95", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "cycle_rank_vs_residue_correlation": _pearson(
            [float(row.get("cycle_rank_proxy", 0.0)) for row in ok_rows],
            [float(row.get("cocycle_residue_rms", 0.0)) for row in ok_rows],
        ),
        "cycle_obstruction_vs_exact_lock_correlation": _pearson(
            [float(row.get("cycle_obstruction_score", 0.0)) for row in ok_rows],
            [float(row.get("exact_lock_score", 0.0)) for row in ok_rows],
        ),
        "residue_vs_concentration_correlation": _pearson(
            [float(row.get("cocycle_residue_rms", 0.0)) for row in ok_rows],
            [float(row.get("mode_concentration_fraction", 0.0)) for row in ok_rows],
        ),
    }

    payload = {
        **CONTROL_CARD,
        "control_card": CONTROL_CARD,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
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
            "lock_eps": float(args.lock_eps),
            "frame": args.frame,
            "frame_limit": args.frame_limit,
        },
        "status": OK_STATUS if counts.get(ERROR_STATUS, 0) == 0 and counts.get(PARTIAL_STATUS, 0) == 0 else PARTIAL_STATUS,
        "warnings": warnings,
        "errors": [],
        "aggregate": aggregate,
        "triad_cycle_obstruction_rows": rows,
    }

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, args.pretty))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
