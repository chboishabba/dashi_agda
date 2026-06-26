#!/usr/bin/env python3
"""Scan resonant-triad incidence and cocycle proxies on the raw N128 archive."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

from ns_boundary_pressure_gate_scan import _frame_indices, _pearson  # type: ignore
from ns_orbit_phase_coherence_scan import (  # type: ignore
    ModeRecord,
    _collect_modes,
    _frame_velocity,
    _json_text,
    _load_raw_bundle,
    _scalar_vorticity_spectrum,
)


SCRIPT_NAME = "scripts/ns_triad_incidence_cocycle_scan.py"
CONTRACT = "ns_triad_incidence_cocycle_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_INCIDENCE_COCYCLE_SCAN"
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
    "ns_triad_incidence_cocycle_scan_N128_20260621.json"
)
DEFAULT_TOP_K = 48
DEFAULT_POOL_MULTIPLIER = 24
DEFAULT_ZERO_EPS = 1.0e-12
DEFAULT_LOCK_EPS = 1.0e-6

CONTROL_CARD = {
    "O": "Measure candidate resonant-triad incidence and cocycle telemetry on the raw N128 archive.",
    "R": (
        "Build a fail-closed carrier from dominant Fourier-vorticity modes, extract resonant selected-mode triads, "
        "assemble an incidence-style triad graph, and track cycle-rank and exact-lock proxies."
    ),
    "C": SCRIPT_NAME,
    "S": "Telemetry only; the incidence/cycle carrier is empirical and non-promoting.",
    "L": (
        "Load raw frames, construct a dominant mode carrier, form resonant triads, "
        "build incidence records, and emit framewise cocycle metrics."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, Clay, or route promotion is inferred from this scan.",
    "F": "A low residual or low cycle rank is still only empirical telemetry, not a proof of solvability or promotion.",
}

AUTHORITY = {
    "candidate_only": True,
    "empirical_non_promoting": True,
    "truth_authority": False,
    "theorem_authority": False,
    "clay_authority": False,
    "runtime_authority": False,
    "promoted": False,
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
    return float(math.remainder(float(angle), 2.0 * math.pi))


def _finite_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _nonnegative_int(value: Any) -> int | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value if value >= 0 else None
    if isinstance(value, float) and math.isfinite(value) and value.is_integer() and value >= 0.0:
        return int(value)
    return None


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


def _dominant_mode(mode_records: list[ModeRecord]) -> ModeRecord | None:
    if not mode_records:
        return None
    return max(mode_records, key=lambda mode: mode.amplitude)


def _mode_key_list(modes: list[ModeRecord]) -> list[list[int]]:
    return [list(mode.key) for mode in modes]


def _triad_incidence_payload(
    modes: list[ModeRecord],
    zero_eps: float,
    lock_eps: float,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    if len(modes) < 3:
        return [], {
            "triad_count": 0,
            "incidence_nonzero_count": 0,
            "incidence_density": 0.0,
            "mode_graph_edge_count": 0,
            "mode_graph_component_count": len(modes),
            "cycle_rank_proxy": 0,
            "cycle_basis_proxy": 0.0,
            "exact_lock_residual_rms": 0.0,
            "exact_lock_residual_max": 0.0,
            "exact_lock_near_lock_fraction": 0.0,
            "exact_lock_score": 0.0,
            "mode_concentration_fraction": 0.0,
            "carrier_shell_radius_mean": 0.0,
            "triad_shell_spread_mean": 0.0,
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
    max_residual = 0.0
    near_lock_weight = 0.0
    triad_shell_spread_total = 0.0

    for i, mode_i in enumerate(modes):
        for j in range(i + 1, len(modes)):
            mode_j = modes[j]
            key_k = (
                mode_i.key[0] + mode_j.key[0],
                mode_i.key[1] + mode_j.key[1],
                mode_i.key[2] + mode_j.key[2],
            )
            k_index = key_to_index.get(key_k)
            if k_index is None or k_index == i or k_index == j:
                continue
            mode_k = modes[k_index]
            weight = mode_i.amplitude * mode_j.amplitude * mode_k.amplitude
            if not math.isfinite(weight) or weight <= float(zero_eps):
                continue

            residual = _wrap_phase(phases[i] + phases[j] - phases[k_index])
            abs_residual = abs(residual)
            triad_records.append(
                {
                    "mode_indices": [int(i), int(j), int(k_index)],
                    "mode_keys": [list(mode_i.key), list(mode_j.key), list(mode_k.key)],
                    "incidence_signs": [1, 1, -1],
                    "weight": float(weight),
                    "phase_mismatch": float(residual),
                    "abs_phase_mismatch": float(abs_residual),
                    "exact_lock_hit": bool(abs_residual <= float(lock_eps)),
                }
            )

            total_weight += float(weight)
            weighted_residual_sq += float(weight) * float(residual * residual)
            max_residual = max(max_residual, abs_residual)
            if abs_residual <= float(lock_eps):
                near_lock_weight += float(weight)
            triad_shell_spread_total += (
                max(mode_i.shell_radius, mode_j.shell_radius, mode_k.shell_radius)
                - min(mode_i.shell_radius, mode_j.shell_radius, mode_k.shell_radius)
            )

            for left, right in ((i, j), (i, k_index), (j, k_index)):
                edge = (left, right) if left < right else (right, left)
                edge_pairs.add(edge)
                union(left, right)

    triad_count = len(triad_records)
    if triad_count == 0:
        return [], {
            "triad_count": 0,
            "incidence_nonzero_count": 0,
            "incidence_density": 0.0,
            "mode_graph_edge_count": len(edge_pairs),
            "mode_graph_component_count": len({find(node) for node in node_indices}),
            "cycle_rank_proxy": 0,
            "cycle_basis_proxy": 0.0,
            "exact_lock_residual_rms": 0.0,
            "exact_lock_residual_max": 0.0,
            "exact_lock_near_lock_fraction": 0.0,
            "exact_lock_score": 0.0,
            "mode_concentration_fraction": mode_concentration_fraction,
            "carrier_shell_radius_mean": carrier_shell_radius_mean,
            "triad_shell_spread_mean": 0.0,
        }

    incidence_nonzero_count = 3 * triad_count
    incidence_density = float(incidence_nonzero_count) / float(len(modes) * triad_count)
    edge_count = len(edge_pairs)
    component_count = len({find(node) for node in node_indices})
    cycle_rank_proxy = max(edge_count - len(modes) + component_count, 0)
    cycle_basis_proxy = float(cycle_rank_proxy) / float(edge_count) if edge_count > 0 else 0.0
    if total_weight > float(zero_eps):
        exact_lock_residual_rms = math.sqrt(weighted_residual_sq / total_weight)
        exact_lock_near_lock_fraction = near_lock_weight / total_weight
    else:
        exact_lock_residual_rms = 0.0
        exact_lock_near_lock_fraction = 0.0
    exact_lock_score = 1.0 / (1.0 + exact_lock_residual_rms)

    metrics = {
        "triad_count": int(triad_count),
        "incidence_nonzero_count": int(incidence_nonzero_count),
        "incidence_density": float(incidence_density),
        "mode_graph_edge_count": int(edge_count),
        "mode_graph_component_count": int(component_count),
        "cycle_rank_proxy": int(cycle_rank_proxy),
        "cycle_basis_proxy": float(cycle_basis_proxy),
        "exact_lock_residual_rms": float(exact_lock_residual_rms),
        "exact_lock_residual_max": float(max_residual),
        "exact_lock_near_lock_fraction": float(exact_lock_near_lock_fraction),
        "exact_lock_score": float(exact_lock_score),
        "mode_concentration_fraction": float(mode_concentration_fraction),
        "carrier_shell_radius_mean": float(carrier_shell_radius_mean),
        "triad_shell_spread_mean": float(triad_shell_spread_total / float(triad_count)),
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
    }
    try:
        u, v, w = _frame_velocity(bundle, snapshot)
        spectrum = _scalar_vorticity_spectrum(u, v, w, bundle.domain_length)
        carrier_modes = _collect_modes(
            spectrum,
            top_k=top_k,
            zero_eps=zero_eps,
            pool_multiplier=pool_multiplier,
        )
        dominant = _dominant_mode(carrier_modes)
        triad_records, metrics = _triad_incidence_payload(
            carrier_modes,
            zero_eps=zero_eps,
            lock_eps=lock_eps,
        )
    except Exception as exc:  # noqa: BLE001
        zero_metrics = {
            "triad_count": 0,
            "incidence_nonzero_count": 0,
            "incidence_density": 0.0,
            "mode_graph_edge_count": 0,
            "mode_graph_component_count": 0,
            "cycle_rank_proxy": 0,
            "cycle_basis_proxy": 0.0,
            "exact_lock_residual_rms": 0.0,
            "exact_lock_residual_max": 0.0,
            "exact_lock_near_lock_fraction": 0.0,
            "exact_lock_score": 0.0,
            "mode_concentration_fraction": 0.0,
            "carrier_shell_radius_mean": 0.0,
            "triad_shell_spread_mean": 0.0,
        }
        row["status"] = ERROR_STATUS
        row["mode_count"] = 0
        row["carrier_mode_count"] = 0
        row["dominant_mode_key"] = None
        row["dominant_mode_amplitude"] = 0.0
        row["dominant_mode_phase"] = 0.0
        row["dominant_mode_shell_radius"] = 0.0
        row["selected_mode_keys"] = []
        row["incidence_records"] = []
        row.update(zero_metrics)
        row["errors"] = [f"frame_triad_incidence_scan_error: {exc}"]
        return ERROR_STATUS, row

    if dominant is None:
        row.update(
            {
                "mode_count": 0,
                "carrier_mode_count": 0,
                "dominant_mode_key": None,
                "dominant_mode_amplitude": 0.0,
                "dominant_mode_phase": 0.0,
                "dominant_mode_shell_radius": 0.0,
                "selected_mode_keys": [],
                "incidence_records": [],
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
            "dominant_mode_key": list(dominant.key),
            "dominant_mode_amplitude": float(dominant.amplitude),
            "dominant_mode_phase": float(dominant.phase),
            "dominant_mode_shell_radius": float(dominant.shell_radius),
            "selected_mode_keys": _mode_key_list(carrier_modes),
            "incidence_records": triad_records,
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
            "triad_incidence_rows": [],
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
            "errors": ["no frames selected for triad incidence scan"],
            "warnings": warnings,
            "triad_incidence_rows": [],
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
        "carrier_mode_count_mean": float(np.mean([row.get("carrier_mode_count", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "triad_count_mean": float(np.mean([row.get("triad_count", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "incidence_density_mean": float(np.mean([row.get("incidence_density", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "cycle_rank_proxy_mean": float(np.mean([row.get("cycle_rank_proxy", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "exact_lock_score_mean": float(np.mean([row.get("exact_lock_score", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "exact_lock_residual_rms_mean": float(np.mean([row.get("exact_lock_residual_rms", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "incidence_density_vs_cycle_rank_correlation": _pearson(
            [float(row.get("incidence_density", 0.0)) for row in ok_rows],
            [float(row.get("cycle_rank_proxy", 0.0)) for row in ok_rows],
        ),
        "exact_lock_score_vs_density_correlation": _pearson(
            [float(row.get("exact_lock_score", 0.0)) for row in ok_rows],
            [float(row.get("incidence_density", 0.0)) for row in ok_rows],
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
        "status": OK_STATUS if counts.get(ERROR_STATUS, 0) == 0 else PARTIAL_STATUS,
        "warnings": warnings,
        "errors": [],
        "aggregate": aggregate,
        "triad_incidence_rows": rows,
    }

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, args.pretty))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
