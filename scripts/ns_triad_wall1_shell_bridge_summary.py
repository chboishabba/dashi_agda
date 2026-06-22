#!/usr/bin/env python3
"""Summarize the active NS triad Wall 1 shell-level telemetry surfaces."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_triad_wall1_shell_bridge_summary.py"
CONTRACT = "ns_triad_wall1_shell_bridge_summary"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_WALL1_SHELL_BRIDGE_SUMMARY"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
ERROR_STATUS = "error"

DEFAULT_PHASE_REGIME_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_phase_regime_separation_scan_N128_20260621.json"
)
DEFAULT_FRAME_STABILITY_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_frame_stability_scan_N128_20260621.json"
)
DEFAULT_COCYCLE_FLOOR_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_cocycle_floor_scan_N128_20260621.json"
)
DEFAULT_CYCLE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_cycle_obstruction_scan_N128_20260621.json"
)
DEFAULT_HESSIAN_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_low_frustration_hessian_scan_N128_20260621.json"
)
DEFAULT_CYCLE_PACKING_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_cycle_packing_overlap_scan_N128_20260622.json"
)
DEFAULT_K01_GEOMETRY_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_k01_geometry_audit_scan_N128_20260621.json"
)
DEFAULT_SCHUR_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_schur_directional_audit_scan_N128_20260622.json"
)
DEFAULT_SIGNED_WALL1_RECONCILIATION_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_signed_carrier_reconciliation_scan_N128_20260622.json"
)
DEFAULT_SIGNED_WALL1_CARRIER_RANKING_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_wall1_carrier_explanatory_rank_scan_N128_20260622.json"
)
DEFAULT_CONTINUOUS_COHERENCE_CAPACITY_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_continuous_coherence_capacity_scan_N128_20260623.json"
)
DEFAULT_K_N_EXACT_IDENTITY_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_exact_identity_scan_N128_20260623.json"
)
DEFAULT_SIGNED_WALL1_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_signed_wall1_theorem_status_20260622.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_wall1_shell_bridge_summary_20260621.json"
)

CONTROL_CARD = {
    "O": "Summarize the active NS triad Wall 1 shell-level telemetry surfaces.",
    "R": (
        "Join the shell-indexed phase-regime, frame-stability, cocycle-floor, cycle-obstruction, "
        "cycle-packing overlap, K01 geometry, Hessian basin, optional Schur directional audit, signed-XOR/signed-spectral Wall 1 receipts, the reconciliation/carrier-ranking scans, and the K_N exact-identity scan into one compact fail-closed Wall 1 summary."
    ),
    "C": SCRIPT_NAME,
    "S": "Candidate-only shell bridge summary; the K_N exact-identity route is fail-closed and the old signed route remains legacy.",
    "L": (
        "Read each shell-level JSON surface plus the signed Wall 1 receipt, the reconciliation/carrier-ranking scans, and the K_N exact-identity surface, normalize onto shared frame-shell keys, "
        "compute compact correlations, and emit explicit unproved Wall 1 markers."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, continuation, or Clay claim is inferred from this bridge summary.",
    "F": "Wall 1 remains unproved; the signed Wall 1 receipt, reconciliation/carrier-ranking scans, and K_N exact-identity surface only sharpen the finite-dimensional telemetry surface.",
}

LOWER_BOUND_SUPPORT_KEYS = (
    "cycle_lower_bound_normalized_max",
    "cycle_lower_bound_normalized_mean",
    "cycle_lower_bound_normalized_sum",
    "family_obstruction_packing_support",
    "cycle_packing_overlap_proxy",
    "cycle_packing_overlap",
    "packing_overlap_proxy",
    "packing_overlap",
    "lower_bound_proxy",
    "mean_cycle_lower_bound",
    "max_cycle_lower_bound",
    "cycle_lower_bound_sum",
)

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
    parser.add_argument("--phase-regime-json", type=Path, default=DEFAULT_PHASE_REGIME_JSON)
    parser.add_argument("--frame-stability-json", type=Path, default=DEFAULT_FRAME_STABILITY_JSON)
    parser.add_argument("--cocycle-floor-json", type=Path, default=DEFAULT_COCYCLE_FLOOR_JSON)
    parser.add_argument("--cycle-json", type=Path, default=DEFAULT_CYCLE_JSON)
    parser.add_argument("--cycle-packing-json", type=Path, default=DEFAULT_CYCLE_PACKING_JSON)
    parser.add_argument("--hessian-json", type=Path, default=DEFAULT_HESSIAN_JSON)
    parser.add_argument("--k01-geometry-json", type=Path, default=DEFAULT_K01_GEOMETRY_JSON)
    parser.add_argument("--schur-json", type=Path, default=DEFAULT_SCHUR_JSON)
    parser.add_argument("--signed-wall1-reconciliation-json", type=Path, default=DEFAULT_SIGNED_WALL1_RECONCILIATION_JSON)
    parser.add_argument("--signed-wall1-carrier-ranking-json", type=Path, default=DEFAULT_SIGNED_WALL1_CARRIER_RANKING_JSON)
    parser.add_argument("--continuous-coherence-capacity-json", type=Path, default=DEFAULT_CONTINUOUS_COHERENCE_CAPACITY_JSON)
    parser.add_argument("--k-n-exact-identity-json", type=Path, default=DEFAULT_K_N_EXACT_IDENTITY_JSON)
    parser.add_argument("--signed-wall1-json", type=Path, default=DEFAULT_SIGNED_WALL1_JSON)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"missing input json: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: payload must be object")
    return payload


def _coerce_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _coerce_int(value: Any) -> int | None:
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value
    if isinstance(value, float) and math.isfinite(value) and value.is_integer():
        return int(value)
    return None


def _rows(payload: dict[str, Any]) -> list[dict[str, Any]]:
    for key in (
        "rows",
        "phase_regime_separation_rows",
        "triad_frame_stability_rows",
        "triad_cycle_obstruction_rows",
        "triad_cycle_packing_rows",
        "cycle_packing_rows",
        "cycle_packing_overlap_rows",
        "family_obstruction_packing_rows",
        "low_frustration_hessian_rows",
        "triad_cocycle_floor_rows",
        "k01_geometry_rows",
        "geometry_rows",
        "continuous_coherence_capacity_rows",
        "continuous_coherence_rows",
        "coherence_capacity_rows",
    ):
        value = payload.get(key)
        if isinstance(value, list):
            return value
    return []


def _first_rows(payload: dict[str, Any], candidate_keys: tuple[str, ...]) -> list[dict[str, Any]]:
    for key in candidate_keys:
        value = payload.get(key)
        if isinstance(value, list):
            return value
    return []


def _first_float(row: dict[str, Any], keys: tuple[str, ...]) -> float | None:
    for key in keys:
        value = _coerce_float(row.get(key))
        if value is not None:
            return value
    return None


def _schur_rows(payload: dict[str, Any]) -> list[dict[str, Any]]:
    for key in (
        "rows",
        "schur_rows",
        "directional_audit_rows",
        "schur_directional_audit_rows",
    ):
        value = payload.get(key)
        if isinstance(value, list):
            return value
    return []


def _payload_status(payload: dict[str, Any] | None) -> str | None:
    if not isinstance(payload, dict):
        return None
    status = payload.get("status")
    if isinstance(status, str):
        return status
    aggregate = payload.get("aggregate")
    if isinstance(aggregate, dict):
        aggregate_status = aggregate.get("status")
        if isinstance(aggregate_status, str):
            return aggregate_status
    return None


def _payload_candidate_only(payload: dict[str, Any] | None) -> bool | None:
    if not isinstance(payload, dict):
        return None
    candidate_only = payload.get("candidate_only")
    if isinstance(candidate_only, bool):
        return candidate_only
    aggregate = payload.get("aggregate")
    if isinstance(aggregate, dict):
        aggregate_candidate_only = aggregate.get("candidate_only")
        if isinstance(aggregate_candidate_only, bool):
            return aggregate_candidate_only
    return None


def _payload_fail_closed(payload: dict[str, Any] | None) -> bool | None:
    if not isinstance(payload, dict):
        return None
    fail_closed = payload.get("fail_closed")
    if isinstance(fail_closed, bool):
        return fail_closed
    aggregate = payload.get("aggregate")
    if isinstance(aggregate, dict):
        aggregate_fail_closed = aggregate.get("fail_closed")
        if isinstance(aggregate_fail_closed, bool):
            return aggregate_fail_closed
    return None


def _effective_fail_closed_status(payload: dict[str, Any] | None) -> str:
    status = _payload_status(payload)
    if status in ("ok", "fail-closed"):
        return "fail-closed"
    return "unavailable"


def _cycle_packing_rows(payload: dict[str, Any]) -> list[dict[str, Any]]:
    return _first_rows(
        payload,
        (
            "triad_cycle_packing_overlap_rows",
            "rows",
            "family_rows",
            "cycle_family_rows",
            "cycle_packing_rows",
            "cycle_packing_overlap_rows",
            "family_obstruction_packing_rows",
            "packing_rows",
            "overlap_rows",
        ),
    )


def _k01_rows(payload: dict[str, Any]) -> list[dict[str, Any]]:
    return _first_rows(
        payload,
        (
            "rows",
            "k01_rows",
            "k01_geometry_rows",
            "geometry_rows",
            "audit_rows",
        ),
    )


def _cocycle_rows(payload: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    top_level_rows = payload.get("triad_cocycle_floor_rows")
    if isinstance(top_level_rows, list):
        for frame_row in top_level_rows:
            if not isinstance(frame_row, dict):
                continue
            frame = _coerce_int(frame_row.get("frame"))
            shell_rows = frame_row.get("shell_rows")
            if isinstance(shell_rows, list):
                for shell_row in shell_rows:
                    if not isinstance(shell_row, dict):
                        continue
                    row = dict(shell_row)
                    if frame is not None and row.get("frame") is None:
                        row["frame"] = frame
                    if row.get("shell") is None:
                        shell = _coerce_int(row.get("shell_cutoff"))
                        if shell is None:
                            shell = _coerce_int(frame_row.get("shell"))
                        if shell is not None:
                            row["shell"] = shell
                    rows.append(row)
                continue
            row = dict(frame_row)
            if frame is not None and row.get("frame") is None:
                row["frame"] = frame
            shell = _coerce_int(row.get("shell"))
            if shell is None:
                shell = _coerce_int(row.get("shell_cutoff"))
            if shell is not None:
                row["shell"] = shell
            rows.append(row)
        return rows

    return _rows(payload)


def _frame_shell_key(row: dict[str, Any]) -> tuple[int, int] | None:
    frame = _coerce_int(row.get("frame"))
    shell = _coerce_int(row.get("shell"))
    if shell is None:
        shell = _coerce_int(row.get("shell_n"))
    if frame is None or shell is None:
        return None
    return int(frame), int(shell)


def _frame_key(row: dict[str, Any]) -> int | None:
    return _coerce_int(row.get("frame"))


def _shell_key(row: dict[str, Any]) -> int | None:
    shell = _coerce_int(row.get("shell"))
    if shell is None:
        shell = _coerce_int(row.get("shell_n"))
    if shell is None:
        shell = _coerce_int(row.get("shell_cutoff"))
    return shell


def _lower_bound_support(row: dict[str, Any]) -> tuple[float | None, str | None, int]:
    preferred_keys = (
        "cycle_lower_bound_normalized_max",
        "cycle_lower_bound_normalized_mean",
        "cycle_lower_bound_normalized_sum",
    )
    available_preferred = [key for key in preferred_keys if _coerce_float(row.get(key)) is not None]
    candidate_keys = available_preferred if available_preferred else list(LOWER_BOUND_SUPPORT_KEYS)
    best_value: float | None = None
    best_source: str | None = None
    support_count = 0
    for key in candidate_keys:
        value = _coerce_float(row.get(key))
        if value is None:
            continue
        support_count += 1
        if best_value is None or value > best_value:
            best_value = value
            best_source = key
    return best_value, best_source, support_count


def _packing_metrics(row: dict[str, Any] | None) -> dict[str, float | None]:
    if row is None:
        return {
            "family_obstruction_packing_support": None,
            "family_obstruction_packing_overlap": None,
            "family_obstruction_packing_lower_bound": None,
            "family_obstruction_packing_ratio": None,
            "cycle_family_support_overlap_mean": None,
            "cycle_family_support_overlap_max": None,
            "cycle_family_support_overlap_density": None,
            "cycle_family_lower_bound_normalized_mean": None,
            "cycle_family_lower_bound_normalized_max": None,
            "cycle_family_lower_bound_normalized_sum": None,
            "cycle_family_lower_bound": None,
            "cycle_family_lower_bound_max": None,
            "cycle_family_packing_concentration": None,
            "cycle_family_obstruction_collapse_score": None,
            "cycle_family_normalized_support_vs_F_max": None,
            "cycle_family_lower_bound_support_over_F_max": None,
            "cycle_family_lower_bound_support_weighted_sum": None,
        }
    support = _first_float(
        row,
        (
            "family_obstruction_packing_support",
            "cycle_family_support_coverage",
            "cycle_family_support_overlap_mean",
            "cycle_family_support_overlap_row_mean",
            "cycle_family_support_overlap_max",
            "cycle_family_support_overlap_density",
            "cycle_family_packing_concentration",
        ),
    )
    overlap = _first_float(
        row,
        (
            "family_obstruction_packing_overlap",
            "cycle_family_support_overlap_max",
            "cycle_family_support_overlap_mean",
            "cycle_family_support_overlap_row_max",
            "cycle_family_support_overlap_density",
        ),
    )
    lower_bound = _first_float(
        row,
        (
            "family_obstruction_packing_lower_bound",
            "cycle_family_lower_bound_normalized_upper",
            "cycle_family_lower_bound_normalized_mean",
            "cycle_family_lower_bound_normalized_max",
            "cycle_family_lower_bound_normalized_sum",
            "cycle_family_lower_bound",
            "cycle_family_lower_bound_max",
        ),
    )
    ratio = _first_float(row, ("family_obstruction_packing_ratio",))
    if ratio is None and support is not None and support > 0.0 and lower_bound is not None:
        ratio = lower_bound / support
    if ratio is None:
        ratio = _first_float(
            row,
            (
                "packing_ratio_proxy",
                "packing_ratio",
                "cycle_family_obstruction_collapse_score",
                "cycle_family_support_overlap_density",
            ),
        )
    return {
        "family_obstruction_packing_support": support,
        "family_obstruction_packing_overlap": overlap,
        "family_obstruction_packing_lower_bound": lower_bound,
        "family_obstruction_packing_ratio": ratio,
        "cycle_family_support_overlap_mean": _first_float(row, ("cycle_family_support_overlap_mean",)),
        "cycle_family_support_overlap_max": _first_float(row, ("cycle_family_support_overlap_max",)),
        "cycle_family_support_overlap_density": _first_float(row, ("cycle_family_support_overlap_density",)),
        "cycle_family_lower_bound_normalized_mean": _first_float(row, ("cycle_family_lower_bound_normalized_mean",)),
        "cycle_family_lower_bound_normalized_max": _first_float(row, ("cycle_family_lower_bound_normalized_max",)),
        "cycle_family_lower_bound_normalized_sum": _first_float(row, ("cycle_family_lower_bound_normalized_sum",)),
        "cycle_family_lower_bound": _first_float(row, ("cycle_family_lower_bound",)),
        "cycle_family_lower_bound_max": _first_float(row, ("cycle_family_lower_bound_max",)),
        "cycle_family_packing_concentration": _first_float(row, ("cycle_family_packing_concentration",)),
        "cycle_family_obstruction_collapse_score": _first_float(row, ("cycle_family_obstruction_collapse_score",)),
        "cycle_family_normalized_support_vs_F_max": _first_float(row, ("cycle_family_normalized_support_vs_F_max",)),
        "cycle_family_lower_bound_support_over_F_max": _first_float(row, ("cycle_family_lower_bound_support_over_F_max",)),
        "cycle_family_lower_bound_support_weighted_sum": _first_float(row, ("cycle_family_lower_bound_support_weighted_sum",)),
    }


def _k01_metrics(row: dict[str, Any] | None) -> dict[str, float | None]:
    if row is None:
        return {
            "k01_geometry_ratio": None,
            "k01_ratio_proxy": None,
            "k01_geometry_signal": None,
            "k01_geometry_lower_bound": None,
            "geometry_alignment_proxy": None,
            "geometry_stability_proxy": None,
            "directional_gap_proxy": None,
            "directional_gap_lower_bound": None,
            "frame_geometry_proxy": None,
            "projection_proxy": None,
            "combined_operator_gap_proxy": None,
            "dangerous_subspace_weight_fraction": None,
            "k01_operator_norm": None,
        }
    ratio = _first_float(row, ("k01_geometry_ratio",))
    ratio_proxy = _first_float(row, ("k01_ratio_proxy",))
    signal = _first_float(
        row,
        (
            "k01_geometry_signal",
            "off_diagonal_share_proxy",
            "directional_off_diagonal_pressure_proxy",
            "off_diagonal_vs_diagonal_ratio",
            "geometry_alignment_proxy",
            "directional_gap_proxy",
            "geometry_stability_proxy",
            "k01_ratio_proxy",
            "k01_geometry_ratio",
        ),
    )
    lower_bound = _first_float(
        row,
        (
            "k01_geometry_lower_bound",
            "directional_gap_lower_bound",
            "directional_gap_proxy",
            "geometry_lower_bound_proxy",
            "geometry_lower_bound",
        ),
    )
    return {
        "k01_geometry_ratio": ratio,
        "k01_ratio_proxy": ratio_proxy,
        "k01_geometry_signal": signal,
        "k01_geometry_lower_bound": lower_bound,
        "geometry_alignment_proxy": _first_float(row, ("geometry_alignment_proxy",)),
        "geometry_stability_proxy": _first_float(row, ("geometry_stability_proxy",)),
        "directional_gap_proxy": _first_float(row, ("directional_gap_proxy",)),
        "directional_gap_lower_bound": _first_float(row, ("directional_gap_lower_bound",)),
        "frame_geometry_proxy": _first_float(row, ("frame_geometry_proxy",)),
        "projection_proxy": _first_float(row, ("projection_proxy",)),
        "combined_operator_gap_proxy": _first_float(row, ("combined_operator_gap_proxy",)),
        "dangerous_subspace_weight_fraction": _first_float(row, ("dangerous_subspace_weight_fraction",)),
        "off_diagonal_share_proxy": _first_float(row, ("off_diagonal_share_proxy",)),
        "directional_off_diagonal_pressure_proxy": _first_float(row, ("directional_off_diagonal_pressure_proxy",)),
        "off_diagonal_vs_diagonal_ratio": _first_float(row, ("off_diagonal_vs_diagonal_ratio",)),
        "k01_operator_norm": _first_float(row, ("k01_operator_norm",)),
    }


def _schur_directional_metrics(row: dict[str, Any]) -> dict[str, float | None]:
    directional_gap = _coerce_float(row.get("schur_directional_gap_proxy"))
    if directional_gap is None:
        directional_gap = _coerce_float(row.get("directional_gap_proxy"))
    directional_lower = _coerce_float(row.get("schur_directional_gap_lower_bound"))
    if directional_lower is None:
        directional_lower = _coerce_float(row.get("directional_gap_lower_bound"))
    directional_residual = _coerce_float(row.get("schur_directional_gap_residual"))
    if directional_residual is None:
        directional_residual = _coerce_float(row.get("directional_gap_residual"))
    directional_ratio = _coerce_float(row.get("schur_directional_gap_ratio"))
    if directional_ratio is None:
        directional_ratio = _coerce_float(row.get("directional_gap_ratio"))
    return {
        "schur_directional_gap_proxy": directional_gap,
        "schur_directional_gap_lower_bound": directional_lower,
        "schur_directional_gap_residual": directional_residual,
        "schur_directional_gap_ratio": directional_ratio,
    }


def _pearson(xs: list[float], ys: list[float]) -> float | None:
    if len(xs) != len(ys) or len(xs) < 2:
        return None
    mean_x = sum(xs) / len(xs)
    mean_y = sum(ys) / len(ys)
    dx = [x - mean_x for x in xs]
    dy = [y - mean_y for y in ys]
    denom_x = math.sqrt(sum(v * v for v in dx))
    denom_y = math.sqrt(sum(v * v for v in dy))
    if denom_x <= 0.0 or denom_y <= 0.0:
        return None
    return sum(a * b for a, b in zip(dx, dy)) / (denom_x * denom_y)


def _mean(values: list[float]) -> float | None:
    return float(sum(values) / len(values)) if values else None


def main() -> int:
    args = _parse_args()
    phase_payload = _read_json(args.phase_regime_json)
    frame_payload = _read_json(args.frame_stability_json)
    cocycle_payload = _read_json(args.cocycle_floor_json)
    cycle_payload = _read_json(args.cycle_json)
    cycle_packing_payload = _read_json(args.cycle_packing_json)
    hessian_payload = _read_json(args.hessian_json)
    k01_geometry_payload = _read_json(args.k01_geometry_json)
    schur_payload = _read_json(args.schur_json) if args.schur_json is not None else {}
    try:
        signed_wall1_reconciliation_payload = _read_json(args.signed_wall1_reconciliation_json)
    except Exception:
        signed_wall1_reconciliation_payload = {}
    try:
        signed_wall1_carrier_ranking_payload = _read_json(args.signed_wall1_carrier_ranking_json)
    except Exception:
        signed_wall1_carrier_ranking_payload = {}
    try:
        continuous_coherence_capacity_payload = _read_json(args.k_n_exact_identity_json)
    except Exception:
        continuous_coherence_capacity_payload = {}
    try:
        signed_wall1_payload = _read_json(args.signed_wall1_json)
    except Exception:
        signed_wall1_payload = {}

    phase_by_key = {key: row for row in _rows(phase_payload) if (key := _frame_shell_key(row)) is not None}
    cocycle_by_key = {key: row for row in _cocycle_rows(cocycle_payload) if (key := _frame_shell_key(row)) is not None}
    frame_by_frame = {key: row for row in _rows(frame_payload) if (key := _frame_key(row)) is not None}
    cycle_by_frame = {key: row for row in _rows(cycle_payload) if (key := _frame_key(row)) is not None}
    cycle_packing_by_key = {key: row for row in _cycle_packing_rows(cycle_packing_payload) if (key := _frame_shell_key(row)) is not None}
    hessian_by_frame = {key: row for row in _rows(hessian_payload) if (key := _frame_key(row)) is not None}
    k01_geometry_by_key = {key: row for row in _k01_rows(k01_geometry_payload) if (key := _frame_shell_key(row)) is not None}
    schur_by_key = {key: row for row in _schur_rows(schur_payload) if (key := _frame_shell_key(row)) is not None}
    signed_wall1_rows = []
    if isinstance(signed_wall1_payload, dict):
        explicit_signed_rows = signed_wall1_payload.get("signed_wall1_rows")
        if isinstance(explicit_signed_rows, list):
            signed_wall1_rows = explicit_signed_rows
    continuous_coherence_capacity_rows = _rows(continuous_coherence_capacity_payload)
    signed_wall1_route_names = None
    if signed_wall1_rows:
        ordered_route_names: list[str] = []
        for row in signed_wall1_rows:
            if not isinstance(row, dict):
                continue
            route_name = row.get("route_name")
            if isinstance(route_name, str) and route_name not in ordered_route_names:
                ordered_route_names.append(route_name)
        signed_wall1_route_names = ordered_route_names
    signed_xor_bridge_open = any(
        isinstance(row, dict)
        and row.get("surface") == "signed_xor_gaugeability"
        and row.get("signed_xor_bridge_open") is True
        for row in signed_wall1_rows
    )
    signed_spectral_bridge_open = any(
        isinstance(row, dict)
        and row.get("surface") == "signed_spectral_frustration"
        and row.get("signed_xor_distance_bridge_open") is True
        for row in signed_wall1_rows
    )
    signed_wall1_candidate_only = (
        all(isinstance(row, dict) and row.get("candidate_only") is True for row in signed_wall1_rows)
        if signed_wall1_rows
        else None
    )
    signed_wall1_fail_closed = (
        all(isinstance(row, dict) and row.get("fail_closed") is True for row in signed_wall1_rows)
        if signed_wall1_rows
        else None
    )
    signed_wall1_theorem_promoted = (
        any(isinstance(row, dict) and row.get("theorem_promoted") is True for row in signed_wall1_rows)
        if signed_wall1_rows
        else None
    )
    signed_wall1_full_ns_promoted = (
        any(isinstance(row, dict) and row.get("full_ns_promoted") is True for row in signed_wall1_rows)
        if signed_wall1_rows
        else None
    )
    signed_wall1_clay_promoted = (
        any(isinstance(row, dict) and row.get("clay_promoted") is True for row in signed_wall1_rows)
        if signed_wall1_rows
        else None
    )
    signed_wall1_reconciliation_input_status = _payload_status(signed_wall1_reconciliation_payload)
    signed_wall1_carrier_ranking_input_status = _payload_status(signed_wall1_carrier_ranking_payload)
    signed_wall1_reconciliation_status = _effective_fail_closed_status(signed_wall1_reconciliation_payload)
    signed_wall1_carrier_ranking_status = _effective_fail_closed_status(signed_wall1_carrier_ranking_payload)
    signed_wall1_carrier_ranking_aggregate = (
        signed_wall1_carrier_ranking_payload.get("aggregate", {})
        if isinstance(signed_wall1_carrier_ranking_payload, dict)
        else {}
    )
    signed_wall1_carrier_top_candidate = (
        signed_wall1_carrier_ranking_aggregate.get("carrier_identification_top_candidate")
        if isinstance(signed_wall1_carrier_ranking_aggregate.get("carrier_identification_top_candidate"), str)
        else None
    )
    signed_wall1_carrier_top_support = _coerce_float(
        signed_wall1_carrier_ranking_aggregate.get("carrier_identification_top_support_mean")
    )
    continuous_coherence_capacity_input_status = _payload_status(continuous_coherence_capacity_payload)
    continuous_coherence_capacity_status = _effective_fail_closed_status(continuous_coherence_capacity_payload)
    continuous_coherence_capacity_candidate_only = _payload_candidate_only(continuous_coherence_capacity_payload)
    continuous_coherence_capacity_fail_closed = _payload_fail_closed(continuous_coherence_capacity_payload)
    continuous_coherence_capacity_aggregate = (
        continuous_coherence_capacity_payload.get("aggregate", {})
        if isinstance(continuous_coherence_capacity_payload, dict)
        else {}
    )
    continuous_coherence_capacity_aggregate_status = _payload_status(continuous_coherence_capacity_aggregate)
    continuous_coherence_capacity_aggregate_candidate_only = _payload_candidate_only(
        continuous_coherence_capacity_aggregate
    )
    continuous_coherence_capacity_aggregate_fail_closed = _payload_fail_closed(
        continuous_coherence_capacity_aggregate
    )
    k_n_exact_identity_input_status = continuous_coherence_capacity_input_status
    k_n_exact_identity_status = continuous_coherence_capacity_status
    k_n_exact_identity_candidate_only = continuous_coherence_capacity_candidate_only
    k_n_exact_identity_fail_closed = continuous_coherence_capacity_fail_closed
    k_n_exact_identity_aggregate_status = continuous_coherence_capacity_aggregate_status
    k_n_exact_identity_aggregate_candidate_only = continuous_coherence_capacity_aggregate_candidate_only
    k_n_exact_identity_aggregate_fail_closed = continuous_coherence_capacity_aggregate_fail_closed
    for row in signed_wall1_rows:
        if not isinstance(row, dict):
            continue
        row["reconciliation_input_status"] = signed_wall1_reconciliation_input_status
        row["reconciliation_status"] = signed_wall1_reconciliation_status
        row["carrier_ranking_input_status"] = signed_wall1_carrier_ranking_input_status
        row["carrier_ranking_status"] = signed_wall1_carrier_ranking_status
    for row in continuous_coherence_capacity_rows:
        if not isinstance(row, dict):
            continue
        row["input_status"] = k_n_exact_identity_input_status
        row["status"] = k_n_exact_identity_status
        row["candidate_only"] = k_n_exact_identity_candidate_only
        row["fail_closed"] = k_n_exact_identity_fail_closed
        row["aggregate_status"] = k_n_exact_identity_aggregate_status
        row["aggregate_candidate_only"] = k_n_exact_identity_aggregate_candidate_only
        row["aggregate_fail_closed"] = k_n_exact_identity_aggregate_fail_closed
        row["continuous_coherence_route_open"] = True
        row["k_n_exact_identity_route_open"] = True
        row["k_n_exact_identity_status"] = k_n_exact_identity_status
        row["continuous_coherence_status"] = k_n_exact_identity_status

    shared_keys = sorted(set(phase_by_key) & set(cocycle_by_key))
    bridge_rows: list[dict[str, Any]] = []
    phase_eps: list[float] = []
    cocycle_bounds: list[float] = []
    max_cocycle_bounds: list[float] = []
    floor_ratios: list[float] = []
    frame_gaps: list[float] = []
    strongest_supports: list[float] = []
    strongest_support_phase_eps: list[float] = []
    strongest_support_frame_gaps: list[float] = []
    strongest_support_xs: list[float] = []
    strongest_support_ys: list[float] = []
    strongest_support_frame_xs: list[float] = []
    strongest_support_frame_ys: list[float] = []
    floor_ratio_xs: list[float] = []
    floor_ratio_ys: list[float] = []
    schur_gap_values: list[float] = []
    schur_gap_lower_bounds: list[float] = []
    schur_gap_residuals: list[float] = []
    schur_gap_ratios: list[float] = []
    packing_supports: list[float] = []
    packing_support_overlaps: list[float] = []
    packing_lower_bounds: list[float] = []
    packing_ratios: list[float] = []
    packing_support_phase_xs: list[float] = []
    packing_support_phase_ys: list[float] = []
    packing_support_floor_xs: list[float] = []
    packing_support_floor_ys: list[float] = []
    packing_support_cycle_xs: list[float] = []
    packing_support_cycle_ys: list[float] = []
    packing_support_k01_xs: list[float] = []
    packing_support_k01_ys: list[float] = []
    k01_signals: list[float] = []
    k01_alignments: list[float] = []
    k01_stabilities: list[float] = []
    k01_directional_gaps: list[float] = []
    k01_signal_phase_xs: list[float] = []
    k01_signal_phase_ys: list[float] = []
    k01_signal_floor_xs: list[float] = []
    k01_signal_floor_ys: list[float] = []
    k01_signal_cycle_xs: list[float] = []
    k01_signal_cycle_ys: list[float] = []
    support_sources: list[str] = []
    support_counts: list[int] = []

    for key in shared_keys:
        frame, shell = key
        phase_row = phase_by_key[key]
        cocycle_row = cocycle_by_key[key]
        frame_row = frame_by_frame.get(frame, {})
        cycle_row = cycle_by_frame.get(frame, {})
        packing_row = cycle_packing_by_key.get(key)
        hessian_row = hessian_by_frame.get(frame, {})
        k01_row = k01_geometry_by_key.get(key)
        schur_row = schur_by_key.get(key, {})
        phase_gap = _coerce_float(phase_row.get("optimized_lambda_gap_proxy"))
        cocycle_bound = _coerce_float(cocycle_row.get("mean_cycle_lower_bound"))
        if cocycle_bound is None:
            cocycle_bound = _coerce_float(cocycle_row.get("lower_bound_proxy"))
        cocycle_max_bound = _coerce_float(cocycle_row.get("max_cycle_lower_bound"))
        floor_ratio = _coerce_float(cocycle_row.get("frustration_floor_ratio_vs_raw"))
        if floor_ratio is None:
            floor_ratio = _coerce_float(cocycle_row.get("floor_ratio_proxy"))
        frame_margin = _coerce_float(frame_row.get("frame_stability_margin_proxy"))
        cycle_rank = _coerce_float(cycle_row.get("cycle_rank_proxy"))
        hessian_proxy = _coerce_float(hessian_row.get("best_reference_hessian_proxy"))
        strongest_support, strongest_source, support_count = _lower_bound_support(cocycle_row)
        cocycle_cycle_defect = _coerce_float(cocycle_row.get("cycle_defect_proxy"))
        cocycle_floor_proxy = _coerce_float(cocycle_row.get("frustration_floor_proxy"))
        packing_metrics = _packing_metrics(packing_row)
        k01_metrics = _k01_metrics(k01_row)
        schur_metrics = _schur_directional_metrics(schur_row)
        bridge_rows.append(
            {
                "frame": int(frame),
                "shell": int(shell),
                "optimized_lambda_gap_proxy": phase_gap,
                "optimized_lambda_max_proxy": _coerce_float(phase_row.get("optimized_lambda_max_proxy")),
                "random_lambda_max_proxy_mean": _coerce_float(phase_row.get("random_lambda_max_proxy_mean")),
                "frustration_floor_ratio_vs_raw": floor_ratio,
                "cycle_lower_bound_normalized_mean": _coerce_float(cocycle_row.get("cycle_lower_bound_normalized_mean")),
                "cycle_lower_bound_normalized_max": _coerce_float(cocycle_row.get("cycle_lower_bound_normalized_max")),
                "cycle_lower_bound_normalized_sum": _coerce_float(cocycle_row.get("cycle_lower_bound_normalized_sum")),
                "mean_cycle_lower_bound": cocycle_bound,
                "max_cycle_lower_bound": cocycle_max_bound,
                "lower_bound_proxy": _coerce_float(cocycle_row.get("lower_bound_proxy")),
                "cycle_defect_proxy": cocycle_cycle_defect,
                "frustration_floor_proxy": cocycle_floor_proxy,
                "family_obstruction_packing_support": packing_metrics["family_obstruction_packing_support"],
                "family_obstruction_packing_overlap": packing_metrics["family_obstruction_packing_overlap"],
                "family_obstruction_packing_lower_bound": packing_metrics["family_obstruction_packing_lower_bound"],
                "family_obstruction_packing_ratio": packing_metrics["family_obstruction_packing_ratio"],
                "cycle_family_support_overlap_mean": packing_metrics["cycle_family_support_overlap_mean"],
                "cycle_family_support_overlap_max": packing_metrics["cycle_family_support_overlap_max"],
                "cycle_family_support_overlap_density": packing_metrics["cycle_family_support_overlap_density"],
                "cycle_family_lower_bound_normalized_mean": packing_metrics["cycle_family_lower_bound_normalized_mean"],
                "cycle_family_lower_bound_normalized_max": packing_metrics["cycle_family_lower_bound_normalized_max"],
                "cycle_family_lower_bound_normalized_sum": packing_metrics["cycle_family_lower_bound_normalized_sum"],
                "cycle_family_lower_bound": packing_metrics["cycle_family_lower_bound"],
                "cycle_family_lower_bound_max": packing_metrics["cycle_family_lower_bound_max"],
                "cycle_family_packing_concentration": packing_metrics["cycle_family_packing_concentration"],
                "cycle_family_obstruction_collapse_score": packing_metrics["cycle_family_obstruction_collapse_score"],
                "cycle_family_normalized_support_vs_F_max": packing_metrics["cycle_family_normalized_support_vs_F_max"],
                "cycle_family_lower_bound_support_over_F_max": packing_metrics["cycle_family_lower_bound_support_over_F_max"],
                "cycle_family_lower_bound_support_weighted_sum": packing_metrics["cycle_family_lower_bound_support_weighted_sum"],
                "k01_geometry_ratio": k01_metrics["k01_geometry_ratio"],
                "k01_ratio_proxy": k01_metrics["k01_ratio_proxy"],
                "k01_geometry_signal": k01_metrics["k01_geometry_signal"],
                "k01_geometry_lower_bound": k01_metrics["k01_geometry_lower_bound"],
                "geometry_alignment_proxy": k01_metrics["geometry_alignment_proxy"],
                "geometry_stability_proxy": k01_metrics["geometry_stability_proxy"],
                "directional_gap_proxy": k01_metrics["directional_gap_proxy"],
                "directional_gap_lower_bound": k01_metrics["directional_gap_lower_bound"],
                "frame_geometry_proxy": k01_metrics["frame_geometry_proxy"],
                "projection_proxy": k01_metrics["projection_proxy"],
                "combined_operator_gap_proxy": k01_metrics["combined_operator_gap_proxy"],
                "dangerous_subspace_weight_fraction": k01_metrics["dangerous_subspace_weight_fraction"],
                "k01_operator_norm": k01_metrics["k01_operator_norm"],
                "strongest_lower_bound_support": strongest_support,
                "strongest_lower_bound_source": strongest_source,
                "strongest_lower_bound_support_count": int(support_count),
                "frame_stability_margin_proxy": frame_margin,
                "cycle_rank_proxy": cycle_rank,
                "best_reference_hessian_proxy": hessian_proxy,
                "signed_wall1_reconciliation_status": signed_wall1_reconciliation_status,
                "signed_wall1_carrier_ranking_status": signed_wall1_carrier_ranking_status,
                "continuous_coherence_capacity_input_status": continuous_coherence_capacity_input_status,
                "continuous_coherence_capacity_status": continuous_coherence_capacity_status,
                "continuous_coherence_capacity_candidate_only": continuous_coherence_capacity_candidate_only,
                "continuous_coherence_capacity_fail_closed": continuous_coherence_capacity_fail_closed,
                "k_n_exact_identity_input_status": k_n_exact_identity_input_status,
                "k_n_exact_identity_status": k_n_exact_identity_status,
                "k_n_exact_identity_candidate_only": k_n_exact_identity_candidate_only,
                "k_n_exact_identity_fail_closed": k_n_exact_identity_fail_closed,
                "k_n_exact_identity_aggregate_status": k_n_exact_identity_aggregate_status,
                "k_n_exact_identity_aggregate_candidate_only": k_n_exact_identity_aggregate_candidate_only,
                "k_n_exact_identity_aggregate_fail_closed": k_n_exact_identity_aggregate_fail_closed,
                **schur_metrics,
            }
        )
        if phase_gap is not None and cocycle_bound is not None:
            phase_eps.append(phase_gap)
            cocycle_bounds.append(cocycle_bound)
        if cocycle_max_bound is not None:
            max_cocycle_bounds.append(cocycle_max_bound)
        if floor_ratio is not None:
            floor_ratios.append(floor_ratio)
        if frame_margin is not None:
            frame_gaps.append(frame_margin)
        if floor_ratio is not None and frame_margin is not None:
            floor_ratio_xs.append(floor_ratio)
            floor_ratio_ys.append(frame_margin)
        if schur_metrics["schur_directional_gap_proxy"] is not None:
            schur_gap_values.append(float(schur_metrics["schur_directional_gap_proxy"]))
        if schur_metrics["schur_directional_gap_lower_bound"] is not None:
            schur_gap_lower_bounds.append(float(schur_metrics["schur_directional_gap_lower_bound"]))
        if schur_metrics["schur_directional_gap_residual"] is not None:
            schur_gap_residuals.append(float(schur_metrics["schur_directional_gap_residual"]))
        if schur_metrics["schur_directional_gap_ratio"] is not None:
            schur_gap_ratios.append(float(schur_metrics["schur_directional_gap_ratio"]))
        if packing_metrics["family_obstruction_packing_support"] is not None:
            support_value = float(packing_metrics["family_obstruction_packing_support"])
            packing_supports.append(support_value)
            if phase_gap is not None:
                packing_support_phase_xs.append(support_value)
                packing_support_phase_ys.append(phase_gap)
            if floor_ratio is not None:
                packing_support_floor_xs.append(support_value)
                packing_support_floor_ys.append(floor_ratio)
            if cocycle_bound is not None:
                packing_support_cycle_xs.append(support_value)
                packing_support_cycle_ys.append(cocycle_bound)
        if packing_metrics["family_obstruction_packing_overlap"] is not None:
            packing_support_overlaps.append(float(packing_metrics["family_obstruction_packing_overlap"]))
        if packing_metrics["family_obstruction_packing_lower_bound"] is not None:
            packing_lower_bounds.append(float(packing_metrics["family_obstruction_packing_lower_bound"]))
        if packing_metrics["family_obstruction_packing_ratio"] is not None:
            packing_ratios.append(float(packing_metrics["family_obstruction_packing_ratio"]))
        if k01_metrics["k01_geometry_signal"] is not None:
            k01_value = float(k01_metrics["k01_geometry_signal"])
            k01_signals.append(k01_value)
            if phase_gap is not None:
                k01_signal_phase_xs.append(k01_value)
                k01_signal_phase_ys.append(phase_gap)
            if floor_ratio is not None:
                k01_signal_floor_xs.append(k01_value)
                k01_signal_floor_ys.append(floor_ratio)
            if cocycle_bound is not None:
                k01_signal_cycle_xs.append(k01_value)
                k01_signal_cycle_ys.append(cocycle_bound)
        if k01_metrics["geometry_alignment_proxy"] is not None:
            k01_alignments.append(float(k01_metrics["geometry_alignment_proxy"]))
        if k01_metrics["geometry_stability_proxy"] is not None:
            k01_stabilities.append(float(k01_metrics["geometry_stability_proxy"]))
        if k01_metrics["directional_gap_proxy"] is not None:
            k01_directional_gaps.append(float(k01_metrics["directional_gap_proxy"]))
        if packing_metrics["family_obstruction_packing_support"] is not None and k01_metrics["k01_geometry_signal"] is not None:
            packing_support_k01_xs.append(float(packing_metrics["family_obstruction_packing_support"]))
            packing_support_k01_ys.append(float(k01_metrics["k01_geometry_signal"]))
        if strongest_support is not None and strongest_source is not None:
            strongest_supports.append(strongest_support)
            if phase_gap is not None:
                strongest_support_phase_eps.append(phase_gap)
                strongest_support_xs.append(strongest_support)
                strongest_support_ys.append(phase_gap)
            if frame_margin is not None:
                strongest_support_frame_gaps.append(frame_margin)
                strongest_support_frame_xs.append(strongest_support)
                strongest_support_frame_ys.append(frame_margin)
            support_sources.append(strongest_source)
            support_counts.append(int(support_count))

    payload = {
        "contract": CONTRACT,
        "schema_version": SCHEMA_VERSION,
        "route_decision": ROUTE_DECISION,
        "script_name": SCRIPT_NAME,
        "control_card": CONTROL_CARD,
        "authority": AUTHORITY,
        "candidate_only": True,
        "empirical_non_promoting": True,
        "fail_closed": True,
        "inputs": {
            "phase_regime_json": str(args.phase_regime_json),
            "frame_stability_json": str(args.frame_stability_json),
            "cocycle_floor_json": str(args.cocycle_floor_json),
            "cycle_json": str(args.cycle_json),
            "cycle_packing_json": str(args.cycle_packing_json),
            "hessian_json": str(args.hessian_json),
            "k01_geometry_json": str(args.k01_geometry_json),
            "schur_json": str(args.schur_json) if args.schur_json is not None else None,
            "signed_wall1_reconciliation_json": str(args.signed_wall1_reconciliation_json)
            if args.signed_wall1_reconciliation_json is not None
            else None,
            "signed_wall1_carrier_ranking_json": str(args.signed_wall1_carrier_ranking_json)
            if args.signed_wall1_carrier_ranking_json is not None
            else None,
            "continuous_coherence_capacity_json": str(args.continuous_coherence_capacity_json)
            if args.continuous_coherence_capacity_json is not None
            else None,
            "k_n_exact_identity_json": str(args.k_n_exact_identity_json)
            if args.k_n_exact_identity_json is not None
            else None,
            "signed_wall1_json": str(args.signed_wall1_json) if args.signed_wall1_json is not None else None,
        },
        "rows": bridge_rows,
        "signed_wall1_rows": signed_wall1_rows,
        "continuous_coherence_capacity_rows": continuous_coherence_capacity_rows,
        "k_n_exact_identity_rows": continuous_coherence_capacity_rows,
        "aggregate": {
            "shared_frame_shell_count": int(len(shared_keys)),
            "shared_frame_count": int(len({frame for frame, _ in shared_keys})),
            "optimized_lambda_gap_proxy_mean": _mean(phase_eps),
            "mean_cycle_lower_bound_mean": _mean(cocycle_bounds),
            "max_cycle_lower_bound_mean": _mean(max_cocycle_bounds),
            "frustration_floor_ratio_vs_raw_mean": _mean(floor_ratios),
            "frame_stability_margin_proxy_mean": _mean(frame_gaps),
            "strongest_lower_bound_support_mean": _mean(strongest_supports),
            "strongest_lower_bound_support_max": max(strongest_supports) if strongest_supports else None,
            "strongest_lower_bound_support_count_mean": _mean([float(value) for value in support_counts]) if support_counts else None,
            "strongest_lower_bound_source_modes": sorted({source for source in support_sources}) if support_sources else [],
            "family_obstruction_packing_support_mean": _mean(packing_supports),
            "family_obstruction_packing_support_max": max(packing_supports) if packing_supports else None,
            "family_obstruction_packing_overlap_mean": _mean(packing_support_overlaps),
            "family_obstruction_packing_overlap_max": max(packing_support_overlaps) if packing_support_overlaps else None,
            "family_obstruction_packing_lower_bound_mean": _mean(packing_lower_bounds),
            "family_obstruction_packing_lower_bound_max": max(packing_lower_bounds) if packing_lower_bounds else None,
            "family_obstruction_packing_ratio_mean": _mean(packing_ratios),
            "family_obstruction_packing_ratio_max": max(packing_ratios) if packing_ratios else None,
            "k01_geometry_signal_mean": _mean(k01_signals),
            "k01_geometry_signal_max": max(k01_signals) if k01_signals else None,
            "geometry_alignment_proxy_mean": _mean(k01_alignments),
            "geometry_alignment_proxy_max": max(k01_alignments) if k01_alignments else None,
            "geometry_stability_proxy_mean": _mean(k01_stabilities),
            "geometry_stability_proxy_max": max(k01_stabilities) if k01_stabilities else None,
            "directional_gap_proxy_mean": _mean(k01_directional_gaps),
            "directional_gap_proxy_max": max(k01_directional_gaps) if k01_directional_gaps else None,
            "phase_gap_vs_cycle_bound_correlation": _pearson(phase_eps, cocycle_bounds),
            "phase_gap_vs_frame_margin_correlation": _pearson(phase_eps, frame_gaps),
            "floor_ratio_vs_frame_margin_correlation": _pearson(floor_ratio_xs, floor_ratio_ys),
            "strongest_lower_bound_support_vs_phase_gap_correlation": _pearson(
                strongest_support_xs,
                strongest_support_ys,
            ),
            "strongest_lower_bound_support_vs_frame_margin_correlation": _pearson(
                strongest_support_frame_xs,
                strongest_support_frame_ys,
            ),
            "family_obstruction_packing_support_vs_phase_gap_correlation": _pearson(
                packing_support_phase_xs,
                packing_support_phase_ys,
            ),
            "family_obstruction_packing_support_vs_floor_ratio_correlation": _pearson(
                packing_support_floor_xs,
                packing_support_floor_ys,
            ),
            "family_obstruction_packing_support_vs_cycle_bound_correlation": _pearson(
                packing_support_cycle_xs,
                packing_support_cycle_ys,
            ),
            "k01_geometry_signal_vs_phase_gap_correlation": _pearson(
                k01_signal_phase_xs,
                k01_signal_phase_ys,
            ),
            "k01_geometry_signal_vs_floor_ratio_correlation": _pearson(
                k01_signal_floor_xs,
                k01_signal_floor_ys,
            ),
            "k01_geometry_signal_vs_cycle_bound_correlation": _pearson(
                k01_signal_cycle_xs,
                k01_signal_cycle_ys,
            ),
            "family_obstruction_packing_support_vs_k01_geometry_signal_correlation": _pearson(
                packing_support_k01_xs,
                packing_support_k01_ys,
            ),
            "schur_directional_gap_proxy_mean": _mean(schur_gap_values),
            "schur_directional_gap_proxy_max": max(schur_gap_values) if schur_gap_values else None,
            "schur_directional_gap_lower_bound_mean": _mean(schur_gap_lower_bounds),
            "schur_directional_gap_residual_mean": _mean(schur_gap_residuals),
            "schur_directional_gap_ratio_mean": _mean(schur_gap_ratios),
            "schur_directional_gap_ratio_max": max(schur_gap_ratios) if schur_gap_ratios else None,
            "schur_directional_audit_status": (
                "fail-closed" if schur_payload and schur_gap_values else "unavailable"
            ),
            "signed_wall1_row_count": int(len(signed_wall1_rows)) if signed_wall1_rows else None,
            "signed_wall1_surface_count": (
                int(
                    len(
                        {
                            row.get("surface")
                            for row in signed_wall1_rows
                            if isinstance(row, dict) and isinstance(row.get("surface"), str)
                        }
                    )
                )
                if signed_wall1_rows
                else None
            ),
            "signed_wall1_status": "fail-closed" if signed_wall1_rows else "unavailable",
            "signed_wall1_candidate_only": signed_wall1_candidate_only,
            "signed_wall1_fail_closed": signed_wall1_fail_closed,
            "signed_wall1_theorem_promoted": signed_wall1_theorem_promoted,
            "signed_wall1_full_ns_promoted": signed_wall1_full_ns_promoted,
            "signed_wall1_clay_promoted": signed_wall1_clay_promoted,
            "signed_wall1_reconciliation_input_status": signed_wall1_reconciliation_input_status,
            "signed_wall1_carrier_ranking_input_status": signed_wall1_carrier_ranking_input_status,
            "signed_wall1_reconciliation_status": signed_wall1_reconciliation_status,
            "signed_wall1_carrier_ranking_status": signed_wall1_carrier_ranking_status,
            "signed_wall1_carrier_top_candidate": signed_wall1_carrier_top_candidate,
            "signed_wall1_carrier_top_support_mean": signed_wall1_carrier_top_support,
            "continuous_coherence_capacity_input_status": continuous_coherence_capacity_input_status,
            "continuous_coherence_capacity_status": continuous_coherence_capacity_status,
            "continuous_coherence_capacity_candidate_only": continuous_coherence_capacity_candidate_only,
            "continuous_coherence_capacity_fail_closed": continuous_coherence_capacity_fail_closed,
            "continuous_coherence_capacity_aggregate_status": continuous_coherence_capacity_aggregate_status,
            "continuous_coherence_capacity_aggregate_candidate_only": continuous_coherence_capacity_aggregate_candidate_only,
            "continuous_coherence_capacity_aggregate_fail_closed": continuous_coherence_capacity_aggregate_fail_closed,
            "k_n_exact_identity_input_status": k_n_exact_identity_input_status,
            "k_n_exact_identity_status": k_n_exact_identity_status,
            "k_n_exact_identity_candidate_only": k_n_exact_identity_candidate_only,
            "k_n_exact_identity_fail_closed": k_n_exact_identity_fail_closed,
            "k_n_exact_identity_aggregate_status": k_n_exact_identity_aggregate_status,
            "k_n_exact_identity_aggregate_candidate_only": k_n_exact_identity_aggregate_candidate_only,
            "k_n_exact_identity_aggregate_fail_closed": k_n_exact_identity_aggregate_fail_closed,
            "continuous_coherence_capacity_aggregate": continuous_coherence_capacity_aggregate,
            "signed_xor_bridge_open": signed_xor_bridge_open if signed_wall1_rows else None,
            "signed_spectral_bridge_open": signed_spectral_bridge_open if signed_wall1_rows else None,
            "signed_surface_consensus": "fail-closed" if signed_wall1_rows else "unavailable",
            "signed_wall1_route_names": signed_wall1_route_names,
            "fail_closed": True,
            "wall1_status": "unproved",
            "theorem_authority": False,
            "clay_authority": False,
        },
    }

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, args.pretty))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
