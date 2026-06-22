#!/usr/bin/env python3
"""Audit cross-shell K01 geometry on the active NS Wall 1 carrier."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_triad_k01_geometry_audit_scan.py"
CONTRACT = "ns_triad_k01_geometry_audit_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_K01_GEOMETRY_AUDIT_SCAN"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, ERROR_STATUS}

DEFAULT_FRAME_STABILITY_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_frame_stability_scan_N128_20260621.json"
)
DEFAULT_SCHUR_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_schur_directional_audit_scan_N128_20260622.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_k01_geometry_audit_scan_N128_20260621.json"
)

CONTROL_CARD = {
    "O": "Measure K01 geometry audit telemetry for the active NS triad Wall 1 route.",
    "R": (
        "Record K01 geometry ratios, directional proxies, and frame-shell consistency "
        "as candidate-only fail-closed telemetry."
    ),
    "C": SCRIPT_NAME,
    "S": "Candidate-only telemetry; the K01 geometry audit is empirical and non-promoting.",
    "L": "Load the audit rows, validate bounded metrics, and expose the wall as unproved.",
    "P": ROUTE_DECISION,
    "G": "No theorem, continuation, or Clay claim is inferred from this audit scan.",
    "F": "K01 geometry telemetry is diagnostic only; fail-closed status is not a proof.",
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
    parser.add_argument("--frame-stability-json", type=Path, default=DEFAULT_FRAME_STABILITY_JSON)
    parser.add_argument("--schur-json", type=Path, default=DEFAULT_SCHUR_JSON)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


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
        return int(value)
    if isinstance(value, float) and math.isfinite(value) and value.is_integer():
        return int(value)
    return None


def _read_json(path: Path) -> tuple[dict[str, Any] | None, list[str], list[str]]:
    warnings: list[str] = []
    errors: list[str] = []
    if not path.exists():
        warnings.append(f"missing input json: {path}")
        return None, warnings, errors
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:  # noqa: BLE001
        errors.append(f"{path}: {exc}")
        return None, warnings, errors
    if not isinstance(payload, dict):
        errors.append(f"{path}: payload must be object")
        return None, warnings, errors
    return payload, warnings, errors


def _rows(payload: dict[str, Any] | None) -> list[dict[str, Any]]:
    if not isinstance(payload, dict):
        return []
    for key in ("rows", "triad_frame_stability_rows"):
        value = payload.get(key)
        if isinstance(value, list):
            return [row for row in value if isinstance(row, dict)]
    return []


def _schur_rows(payload: dict[str, Any] | None) -> list[dict[str, Any]]:
    if not isinstance(payload, dict):
        return []
    for key in ("rows", "schur_rows", "directional_audit_rows", "schur_directional_audit_rows"):
        value = payload.get(key)
        if isinstance(value, list):
            return [row for row in value if isinstance(row, dict)]
    return []


def _frame_key(row: dict[str, Any]) -> int | None:
    return _coerce_int(row.get("frame"))


def _frame_shell_key(row: dict[str, Any]) -> tuple[int, int] | None:
    frame = _coerce_int(row.get("frame"))
    shell = _coerce_int(row.get("shell"))
    if shell is None:
        shell = _coerce_int(row.get("shell_n"))
    if shell is None:
        shell = _coerce_int(row.get("shell_cutoff"))
    if frame is None or shell is None:
        return None
    return int(frame), int(shell)


def _mean(values: list[float]) -> float | None:
    return float(sum(values) / len(values)) if values else None


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


def _safe_ratio(numerator: float | None, denominator: float | None) -> float | None:
    if numerator is None or denominator is None:
        return None
    if denominator <= 0.0:
        return None
    value = float(numerator) / float(denominator)
    return value if math.isfinite(value) else None


def _nz_float(value: float | None) -> float:
    return float(value) if value is not None and math.isfinite(float(value)) else 0.0


def _nz_int(value: int | None) -> int:
    return int(value) if value is not None else 0


def _shell_geometry_metrics(frame_row: dict[str, Any], schur_row: dict[str, Any]) -> dict[str, Any]:
    low = _coerce_float(schur_row.get("low_block_size"))
    high = _coerce_float(schur_row.get("high_block_size"))
    total = None
    if low is not None and high is not None:
        total = low + high

    k00 = _coerce_float(schur_row.get("k00_lambda_max"))
    k01 = _coerce_float(schur_row.get("k01_operator_norm"))
    k11 = _coerce_float(schur_row.get("k11_lambda_max"))
    directional_gap = _coerce_float(schur_row.get("schur_directional_gap_proxy"))
    directional_lower = _coerce_float(schur_row.get("schur_directional_gap_lower_bound"))
    directional_residual = _coerce_float(schur_row.get("schur_directional_gap_residual"))
    coupling_concentration = _coerce_float(schur_row.get("dangerous_subspace_weight_fraction"))
    frame_margin = _coerce_float(frame_row.get("frame_stability_margin_proxy"))
    positive_gap = _coerce_float(frame_row.get("positive_backbone_operator_gap_proxy"))
    negative_gap = _coerce_float(frame_row.get("negative_frame_operator_gap_proxy"))
    combined_gap = _coerce_float(frame_row.get("combined_operator_gap_proxy"))
    frame_stability = _coerce_float(frame_row.get("frame_stability_proxy"))

    shell_ratio = _safe_ratio(high, low if low is not None and low > 0.0 else None)
    shell_fraction = _safe_ratio(high, total)
    shell_imbalance = None
    if low is not None and high is not None:
        shell_imbalance = abs(high - low) / max(low + high, 1.0)

    k01_geometry_ratio = None
    if k01 is not None:
        denom_terms = [abs(value) for value in (k00, k01, k11) if value is not None]
        denom = sum(denom_terms)
        if denom > 0.0:
            k01_geometry_ratio = abs(k01) / denom

    angular_mismatch_proxy = None
    if directional_gap is not None or directional_residual is not None:
        base = abs(directional_gap) if directional_gap is not None else 0.0
        residual = abs(directional_residual) if directional_residual is not None else 0.0
        angular_mismatch_proxy = math.atan2(residual, max(base, 1.0e-12))

    geometry_alignment_proxy = None
    if angular_mismatch_proxy is not None:
        geometry_alignment_proxy = 1.0 / (1.0 + angular_mismatch_proxy)

    frame_geometry_proxy = combined_gap if combined_gap is not None else frame_stability
    incompressibility_proxy = positive_gap if positive_gap is not None else frame_margin
    projection_proxy = negative_gap if negative_gap is not None else combined_gap

    off_diagonal_vs_diagonal_ratio = None
    if k01 is not None and (k00 is not None or k11 is not None):
        diagonal_scale = abs(k00 or 0.0) + abs(k11 or 0.0)
        off_diagonal_vs_diagonal_ratio = abs(k01) / max(diagonal_scale, 1.0e-12)

    k01_to_k00_ratio = _safe_ratio(abs(k01) if k01 is not None else None, abs(k00) if k00 is not None else None)
    k01_to_k11_ratio = _safe_ratio(abs(k01) if k01 is not None else None, abs(k11) if k11 is not None else None)
    off_diagonal_share_proxy = None
    if k01 is not None:
        denom = sum(abs(value) for value in (k00, k01, k11) if value is not None)
        off_diagonal_share_proxy = abs(k01) / max(denom, 1.0e-12)
    off_diagonal_contrast_proxy = None
    if k01 is not None and (k00 is not None or k11 is not None):
        off_diagonal_contrast_proxy = abs(k01) / max(abs((k00 or 0.0) - (k11 or 0.0)), 1.0e-12)

    directional_gap_ratio = None
    if directional_gap is not None and directional_lower is not None:
        directional_gap_ratio = directional_gap / max(abs(directional_lower), 1.0e-12)

    directional_gap_residual_ratio = None
    if directional_residual is not None and directional_gap is not None:
        directional_gap_residual_ratio = directional_residual / max(abs(directional_gap), 1.0e-12)

    off_diagonal_pressure_proxy = None
    if off_diagonal_vs_diagonal_ratio is not None and shell_imbalance is not None:
        off_diagonal_pressure_proxy = off_diagonal_vs_diagonal_ratio * shell_imbalance

    directional_off_diagonal_pressure_proxy = None
    if directional_gap is not None and off_diagonal_share_proxy is not None:
        directional_off_diagonal_pressure_proxy = abs(directional_gap) * off_diagonal_share_proxy

    core_available = sum(
        1
        for value in (
            low,
            high,
            k00,
            k01,
            k11,
            directional_gap,
            directional_lower,
            directional_residual,
        )
        if value is not None
    )
    geometry_completeness = core_available / 8.0
    if core_available >= 7:
        geometry_sufficiency = "full"
    elif core_available >= 4:
        geometry_sufficiency = "partial"
    else:
        geometry_sufficiency = "insufficient"

    return {
        "k00_lambda_max": k00,
        "k01_operator_norm": k01,
        "k11_lambda_max": k11,
        "low_block_size": low,
        "high_block_size": high,
        "shell_ratio": shell_ratio,
        "shell_fraction": shell_fraction,
        "shell_imbalance": shell_imbalance,
        "shell_curvature_proxy": shell_imbalance,
        "k01_geometry_ratio": k01_geometry_ratio,
        "k01_ratio_proxy": k01_geometry_ratio,
        "off_diagonal_vs_diagonal_ratio": off_diagonal_vs_diagonal_ratio,
        "k01_to_k00_ratio": k01_to_k00_ratio,
        "k01_to_k11_ratio": k01_to_k11_ratio,
        "off_diagonal_share_proxy": off_diagonal_share_proxy,
        "off_diagonal_contrast_proxy": off_diagonal_contrast_proxy,
        "angular_mismatch_proxy": angular_mismatch_proxy,
        "frame_geometry_proxy": frame_geometry_proxy,
        "incompressibility_proxy": incompressibility_proxy,
        "projection_proxy": projection_proxy,
        "directional_gap_proxy": directional_gap,
        "directional_gap_lower_bound": directional_lower,
        "directional_gap_residual": directional_residual,
        "directional_gap_ratio": directional_gap_ratio,
        "directional_gap_residual_ratio": directional_gap_residual_ratio,
        "off_diagonal_pressure_proxy": off_diagonal_pressure_proxy,
        "directional_off_diagonal_pressure_proxy": directional_off_diagonal_pressure_proxy,
        "geometry_stability_proxy": frame_margin,
        "geometry_alignment_proxy": geometry_alignment_proxy,
        "coupling_concentration": coupling_concentration,
        "dangerous_subspace_weight_fraction": coupling_concentration,
        "geometry_completeness": geometry_completeness,
        "geometry_sufficiency": geometry_sufficiency,
    }


def _source_surface(
    name: str,
    path: Path,
    payload: dict[str, Any] | None,
    load_warnings: list[str],
    load_errors: list[str],
) -> dict[str, Any]:
    rows = _schur_rows(payload) if name == "schur" else _rows(payload)
    frames = {frame for row in rows if (frame := _frame_key(row)) is not None}
    frame_shells = {key for row in rows if (key := _frame_shell_key(row)) is not None}
    status = "ok"
    if payload is None and load_errors:
        status = "error"
    elif payload is None:
        status = "missing"
    elif not rows:
        status = "empty"
    return {
        "name": name,
        "path": str(path),
        "present": payload is not None,
        "status": status,
        "row_count": int(len(rows)),
        "frame_count": int(len(frames)),
        "frame_shell_count": int(len(frame_shells)),
        "warnings": list(load_warnings),
        "errors": list(load_errors),
    }


def _row(
    frame: int,
    shell: int,
    frame_row: dict[str, Any],
    schur_row: dict[str, Any],
) -> tuple[str, dict[str, Any]]:
    metrics = _shell_geometry_metrics(frame_row, schur_row)
    warnings: list[str] = []
    errors: list[str] = []

    row: dict[str, Any] = {
        "frame": int(frame),
        "snapshot_index": _coerce_int(schur_row.get("snapshot_index")) if _coerce_int(schur_row.get("snapshot_index")) is not None else int(frame),
        "shell": int(shell),
        "source": str(schur_row.get("source") or frame_row.get("source") or "unknown"),
        "route_mode": "fail-closed",
        "candidate_only": True,
        "empirical_non_promoting": True,
        "fail_closed": True,
        "wall1_status": "unproved",
        "wall1_proved": False,
        "join_status": "shared-frame-shell",
        "shell_partition_kind": "dangerous_high_shell",
        "dangerous_shell_partition": "high",
        "dangerous_shell_is_high": True,
        "selected_mode_count": _nz_int(
            _coerce_int(schur_row.get("selected_mode_count"))
            if _coerce_int(schur_row.get("selected_mode_count")) is not None
            else _coerce_int(frame_row.get("selected_mode_count"))
        ),
        "triad_count": _nz_int(
            _coerce_int(schur_row.get("triad_count"))
            if _coerce_int(schur_row.get("triad_count")) is not None
            else _coerce_int(frame_row.get("triad_count"))
        ),
        "carrier_stratum_count": _nz_int(
            _coerce_int(schur_row.get("carrier_stratum_count"))
            if _coerce_int(schur_row.get("carrier_stratum_count")) is not None
            else _coerce_int(frame_row.get("carrier_stratum_count"))
        ),
        "k00_lambda_max": metrics["k00_lambda_max"],
        "k01_operator_norm": metrics["k01_operator_norm"],
        "k11_lambda_max": metrics["k11_lambda_max"],
        "low_block_size": int(metrics["low_block_size"]) if metrics["low_block_size"] is not None else 0,
        "high_block_size": int(metrics["high_block_size"]) if metrics["high_block_size"] is not None else 0,
        "shell_ratio": metrics["shell_ratio"],
        "shell_fraction": metrics["shell_fraction"],
        "shell_imbalance": metrics["shell_imbalance"],
        "shell_curvature_proxy": metrics["shell_curvature_proxy"],
        "k01_geometry_ratio": metrics["k01_geometry_ratio"],
        "k01_ratio_proxy": metrics["k01_ratio_proxy"],
        "off_diagonal_vs_diagonal_ratio": metrics["off_diagonal_vs_diagonal_ratio"],
        "k01_to_k00_ratio": metrics["k01_to_k00_ratio"],
        "k01_to_k11_ratio": metrics["k01_to_k11_ratio"],
        "off_diagonal_share_proxy": metrics["off_diagonal_share_proxy"],
        "off_diagonal_contrast_proxy": metrics["off_diagonal_contrast_proxy"],
        "angular_mismatch_proxy": metrics["angular_mismatch_proxy"],
        "frame_geometry_proxy": metrics["frame_geometry_proxy"],
        "incompressibility_proxy": metrics["incompressibility_proxy"],
        "projection_proxy": metrics["projection_proxy"],
        "directional_gap_proxy": metrics["directional_gap_proxy"],
        "directional_gap_lower_bound": metrics["directional_gap_lower_bound"],
        "directional_gap_residual": metrics["directional_gap_residual"],
        "directional_gap_ratio": metrics["directional_gap_ratio"],
        "directional_gap_residual_ratio": metrics["directional_gap_residual_ratio"],
        "off_diagonal_pressure_proxy": metrics["off_diagonal_pressure_proxy"],
        "directional_off_diagonal_pressure_proxy": metrics["directional_off_diagonal_pressure_proxy"],
        "geometry_stability_proxy": metrics["geometry_stability_proxy"],
        "geometry_alignment_proxy": metrics["geometry_alignment_proxy"],
        "coupling_concentration": metrics["coupling_concentration"],
        "dangerous_subspace_weight_fraction": metrics["dangerous_subspace_weight_fraction"],
        "geometry_completeness": metrics["geometry_completeness"],
        "geometry_sufficiency": metrics["geometry_sufficiency"],
        "frame_stability_margin_proxy": _coerce_float(frame_row.get("frame_stability_margin_proxy")),
        "positive_backbone_operator_gap_proxy": _coerce_float(frame_row.get("positive_backbone_operator_gap_proxy")),
        "negative_frame_operator_gap_proxy": _coerce_float(frame_row.get("negative_frame_operator_gap_proxy")),
        "combined_operator_gap_proxy": _coerce_float(frame_row.get("combined_operator_gap_proxy")),
        "frame_stability_proxy": _coerce_float(frame_row.get("frame_stability_proxy")),
        "selected_mode_amplitude_sum": _coerce_float(frame_row.get("selected_mode_amplitude_sum")),
        "mode_concentration_fraction": _coerce_float(frame_row.get("mode_concentration_fraction")),
        "carrier_shell_radius_mean": _coerce_float(frame_row.get("carrier_shell_radius_mean")),
        "carrier_shell_radius_p95": _coerce_float(frame_row.get("carrier_shell_radius_p95")),
        "backbone_vs_negative_gap_ratio": _coerce_float(frame_row.get("backbone_vs_negative_gap_ratio")),
        "stratum_cross_mass_ratio": _coerce_float(frame_row.get("stratum_cross_mass_ratio")),
        "stratum_internal_mass_ratio": _coerce_float(frame_row.get("stratum_internal_mass_ratio")),
        "stratum_balance_entropy_normalized": _coerce_float(frame_row.get("stratum_balance_entropy_normalized")),
        "triad_phase_coherence_mean": _coerce_float(frame_row.get("triad_phase_coherence_mean")),
        "triad_phase_coherence_abs_mean": _coerce_float(frame_row.get("triad_phase_coherence_abs_mean")),
        "triad_shell_spread_mean": _coerce_float(frame_row.get("triad_shell_spread_mean")),
        "triad_shell_spread_p95": _coerce_float(frame_row.get("triad_shell_spread_p95")),
    }

    required = (
        "shell_ratio",
        "angular_mismatch_proxy",
        "incompressibility_proxy",
        "projection_proxy",
        "coupling_concentration",
    )
    if any(metrics[key] is None for key in required):
        warnings.append("one or more shell geometry proxies are unavailable")
        status = PARTIAL_STATUS
    else:
        status = OK_STATUS

    if metrics["k01_geometry_ratio"] is None:
        warnings.append("k01 geometry ratio unavailable")
        status = PARTIAL_STATUS if status == OK_STATUS else status
    if metrics["directional_gap_proxy"] is None or metrics["directional_gap_lower_bound"] is None:
        warnings.append("directional Schur gaps unavailable")
        status = PARTIAL_STATUS if status == OK_STATUS else status
    if metrics["geometry_sufficiency"] != "full":
        warnings.append(f"geometry sufficiency is {metrics['geometry_sufficiency']}")
        status = PARTIAL_STATUS if status == OK_STATUS else status
    if metrics["shell_ratio"] is not None and metrics["shell_ratio"] < 0.0:
        errors.append("shell_ratio: must be nonnegative")
        status = ERROR_STATUS

    row["status"] = status
    if warnings:
        row["warnings"] = warnings
    if errors:
        row["errors"] = errors
    return status, row


def _fallback_row(message: str) -> dict[str, Any]:
    return {
        "frame": 0,
        "snapshot_index": 0,
        "shell": 0,
        "source": "unavailable",
        "route_mode": "fail-closed",
        "candidate_only": True,
        "empirical_non_promoting": True,
        "fail_closed": True,
        "wall1_status": "unproved",
        "wall1_proved": False,
        "dangerous_shell_partition": "unavailable",
        "dangerous_shell_is_high": False,
        "join_status": "insufficient",
        "shell_partition_kind": "insufficient",
        "selected_mode_count": 0,
        "triad_count": 0,
        "carrier_stratum_count": 0,
        "k00_lambda_max": 0.0,
        "k01_operator_norm": 0.0,
        "k11_lambda_max": 0.0,
        "low_block_size": 0,
        "high_block_size": 0,
        "shell_ratio": 0.0,
        "shell_fraction": 0.0,
        "shell_imbalance": 0.0,
        "shell_curvature_proxy": 0.0,
        "k01_geometry_ratio": 0.0,
        "k01_ratio_proxy": 0.0,
        "off_diagonal_vs_diagonal_ratio": 0.0,
        "k01_to_k00_ratio": 0.0,
        "k01_to_k11_ratio": 0.0,
        "off_diagonal_share_proxy": 0.0,
        "off_diagonal_contrast_proxy": 0.0,
        "angular_mismatch_proxy": 0.0,
        "frame_geometry_proxy": 0.0,
        "incompressibility_proxy": 0.0,
        "projection_proxy": 0.0,
        "directional_gap_proxy": 0.0,
        "directional_gap_lower_bound": 0.0,
        "directional_gap_residual": 0.0,
        "directional_gap_ratio": 0.0,
        "directional_gap_residual_ratio": 0.0,
        "off_diagonal_pressure_proxy": 0.0,
        "directional_off_diagonal_pressure_proxy": 0.0,
        "geometry_stability_proxy": 0.0,
        "geometry_alignment_proxy": 0.0,
        "coupling_concentration": 0.0,
        "dangerous_subspace_weight_fraction": 0.0,
        "geometry_completeness": 0.0,
        "geometry_sufficiency": "insufficient",
        "status": ERROR_STATUS,
        "warnings": [message],
        "errors": [message],
    }


def _aggregate(rows: list[dict[str, Any]]) -> dict[str, Any]:
    ok_rows = [row for row in rows if row.get("status") == OK_STATUS]
    partial_rows = [row for row in rows if row.get("status") == PARTIAL_STATUS]
    error_rows = [row for row in rows if row.get("status") == ERROR_STATUS]

    def _series(key: str, pool: list[dict[str, Any]] = ok_rows) -> list[float]:
        values: list[float] = []
        for row in pool:
            value = _coerce_float(row.get(key))
            if value is not None:
                values.append(value)
        return values

    shell_ratio_values = _series("shell_ratio")
    angular_values = _series("angular_mismatch_proxy")
    k01_ratio_values = _series("k01_geometry_ratio")
    off_diagonal_ratio_values = _series("off_diagonal_vs_diagonal_ratio")
    off_diagonal_share_values = _series("off_diagonal_share_proxy")
    off_diagonal_contrast_values = _series("off_diagonal_contrast_proxy")
    frame_geometry_values = _series("frame_geometry_proxy")
    directional_values = _series("directional_gap_proxy")
    directional_lower_values = _series("directional_gap_lower_bound")
    directional_residual_values = _series("directional_gap_residual")
    directional_ratio_values = _series("directional_gap_ratio")
    directional_residual_ratio_values = _series("directional_gap_residual_ratio")
    off_diagonal_pressure_values = _series("off_diagonal_pressure_proxy")
    directional_off_diagonal_pressure_values = _series("directional_off_diagonal_pressure_proxy")
    geometry_stability_values = _series("geometry_stability_proxy")
    geometry_alignment_values = _series("geometry_alignment_proxy")
    incompressibility_values = _series("incompressibility_proxy")
    projection_values = _series("projection_proxy")
    coupling_values = _series("coupling_concentration")
    geometry_completeness_values = _series("geometry_completeness")
    sufficiency_counts = {
        "full": int(sum(1 for row in rows if row.get("geometry_sufficiency") == "full")),
        "partial": int(sum(1 for row in rows if row.get("geometry_sufficiency") == "partial")),
        "insufficient": int(sum(1 for row in rows if row.get("geometry_sufficiency") == "insufficient")),
    }

    return {
        "processed_rows": int(len(rows)),
        "shared_frame_shell_count": int(len(rows)),
        "shared_frame_count": int(len({row.get("frame") for row in rows if _coerce_int(row.get("frame")) is not None})),
        "shared_shell_count": int(len({row.get("shell") for row in rows if _coerce_int(row.get("shell")) is not None})),
        "ok_rows": int(len(ok_rows)),
        "partial_rows": int(len(partial_rows)),
        "error_rows": int(len(error_rows)),
        "k01_geometry_ratio_mean": _mean(k01_ratio_values),
        "k01_geometry_ratio_max": max(k01_ratio_values) if k01_ratio_values else None,
        "off_diagonal_vs_diagonal_ratio_mean": _mean(off_diagonal_ratio_values),
        "off_diagonal_share_proxy_mean": _mean(off_diagonal_share_values),
        "off_diagonal_contrast_proxy_mean": _mean(off_diagonal_contrast_values),
        "frame_geometry_proxy_mean": _mean(frame_geometry_values),
        "directional_gap_proxy_mean": _mean(directional_values),
        "directional_gap_lower_bound_mean": _mean(directional_lower_values),
        "directional_gap_residual_mean": _mean(directional_residual_values),
        "directional_gap_ratio_mean": _mean(directional_ratio_values),
        "directional_gap_residual_ratio_mean": _mean(directional_residual_ratio_values),
        "off_diagonal_pressure_proxy_mean": _mean(off_diagonal_pressure_values),
        "directional_off_diagonal_pressure_proxy_mean": _mean(directional_off_diagonal_pressure_values),
        "geometry_stability_proxy_mean": _mean(geometry_stability_values),
        "geometry_alignment_proxy_mean": _mean(geometry_alignment_values),
        "shell_ratio_mean": _mean(shell_ratio_values),
        "shell_ratio_max": max(shell_ratio_values) if shell_ratio_values else None,
        "angular_mismatch_proxy_mean": _mean(angular_values),
        "angular_mismatch_proxy_max": max(angular_values) if angular_values else None,
        "incompressibility_proxy_mean": _mean(incompressibility_values),
        "projection_proxy_mean": _mean(projection_values),
        "coupling_concentration_mean": _mean(coupling_values),
        "coupling_concentration_max": max(coupling_values) if coupling_values else None,
        "dangerous_subspace_weight_fraction_mean": _mean(coupling_values),
        "dangerous_subspace_weight_fraction_max": max(coupling_values) if coupling_values else None,
        "geometry_completeness_mean": _mean(geometry_completeness_values),
        "geometry_sufficiency_counts": sufficiency_counts,
        "shell_ratio_vs_coupling_concentration_correlation": _pearson(shell_ratio_values, coupling_values),
        "angular_mismatch_vs_directional_gap_correlation": _pearson(angular_values, directional_values),
        "k01_geometry_ratio_vs_geometry_stability_correlation": _pearson(k01_ratio_values, geometry_stability_values),
        "coupling_concentration_vs_geometry_alignment_correlation": _pearson(coupling_values, geometry_alignment_values),
        "wall1_status": "unproved",
        "wall1_proved": False,
        "candidate_only": True,
        "empirical_non_promoting": True,
        "fail_closed": True,
        "theorem_authority": False,
        "clay_authority": False,
    }


def main() -> int:
    args = _parse_args()
    warnings: list[str] = []
    errors: list[str] = []

    frame_payload, frame_warnings, frame_errors = _read_json(args.frame_stability_json)
    schur_payload, schur_warnings, schur_errors = _read_json(args.schur_json)
    warnings.extend(frame_warnings)
    warnings.extend(schur_warnings)
    errors.extend(frame_errors)
    errors.extend(schur_errors)

    frame_rows = _rows(frame_payload)
    schur_rows = _schur_rows(schur_payload)
    frame_by_frame = {key: row for row in frame_rows if (key := _frame_key(row)) is not None}
    schur_by_key = {key: row for row in schur_rows if (key := _frame_shell_key(row)) is not None}
    shell_values = {shell for _, shell in schur_by_key}
    shared_keys = sorted(set(schur_by_key) & {(frame, shell) for frame in frame_by_frame for shell in shell_values})

    source_surfaces = [
        _source_surface("frame_stability", args.frame_stability_json, frame_payload, frame_warnings, frame_errors),
        _source_surface("schur", args.schur_json, schur_payload, schur_warnings, schur_errors),
    ]

    rows: list[dict[str, Any]] = []
    for frame, shell in shared_keys:
        frame_row = frame_by_frame.get(frame)
        schur_row = schur_by_key.get((frame, shell))
        if frame_row is None or schur_row is None:
            continue
        _status, row = _row(frame, shell, frame_row, schur_row)
        rows.append(row)

    if not rows:
        message = "no shared frame-shell telemetry available"
        warnings.append(message)
        if not errors:
            errors.append(message)
        rows = [_fallback_row(message)]

    aggregate = _aggregate(rows)
    aggregate["source_surface_count"] = int(len(source_surfaces))
    aggregate["present_surface_count"] = int(sum(1 for surface in source_surfaces if surface.get("present") is True))
    aggregate["wall1_status"] = "unproved"
    aggregate["wall1_proved"] = False
    aggregate["candidate_only"] = True
    aggregate["empirical_non_promoting"] = True
    aggregate["fail_closed"] = True
    aggregate["theorem_authority"] = False
    aggregate["clay_authority"] = False

    has_error_rows = any(row.get("status") == ERROR_STATUS for row in rows)
    has_partial_rows = any(row.get("status") == PARTIAL_STATUS for row in rows)
    status = ERROR_STATUS if has_error_rows or errors else PARTIAL_STATUS if has_partial_rows or warnings else OK_STATUS
    ok = status == OK_STATUS

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
        "wall1_status": "unproved",
        "wall1_proved": False,
        "inputs": {
            "frame_stability_json": str(args.frame_stability_json),
            "schur_json": str(args.schur_json),
            "output_json": str(args.output_json),
        },
        "source_surfaces": source_surfaces,
        "rows": rows,
        "aggregate": aggregate,
        "warnings": warnings,
        "errors": errors,
        "status": status,
        "ok": ok,
    }

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    text = _json_text(payload, args.pretty)
    args.output_json.write_text(text + "\n", encoding="utf-8")
    print(text)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
