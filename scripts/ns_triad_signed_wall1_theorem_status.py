#!/usr/bin/env python3
"""Summarize signed Wall 1 theorem-facing surfaces and emit JSON plus CSV."""

from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
from typing import Any

SCRIPT_NAME = "scripts/ns_triad_signed_wall1_theorem_status.py"
CONTRACT = "ns_triad_signed_wall1_theorem_status"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_SIGNED_WALL1_THEOREM_STATUS"
SCHEMA_VERSION = "1.0.0"

DEFAULT_GAUGEABILITY_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_signed_xor_gaugeability_scan_N128_20260622.json"
)
DEFAULT_SPECTRAL_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_signed_spectral_audit_scan_N128_20260622.json"
)
DEFAULT_COCYCLE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_cocycle_floor_scan_N128_20260621.json"
)
DEFAULT_SCHUR_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_schur_directional_audit_scan_N128_20260622.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_signed_wall1_theorem_status_20260622.json"
)
DEFAULT_OUTPUT_CSV = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "wall1_theorem_status.csv"
)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gaugeability-json", type=Path, default=DEFAULT_GAUGEABILITY_JSON)
    parser.add_argument("--spectral-json", type=Path, default=DEFAULT_SPECTRAL_JSON)
    parser.add_argument("--cocycle-json", type=Path, default=DEFAULT_COCYCLE_JSON)
    parser.add_argument("--schur-json", type=Path, default=DEFAULT_SCHUR_JSON)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--output-csv", type=Path, default=DEFAULT_OUTPUT_CSV)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _rows(payload: dict[str, Any]) -> list[dict[str, Any]]:
    for key in ("rows", "triad_cocycle_floor_rows", "schur_rows"):
        value = payload.get(key)
        if isinstance(value, list):
            return value
    return []


def _cocycle_rows(payload: dict[str, Any]) -> list[dict[str, Any]]:
    rows = payload.get("rows")
    if isinstance(rows, list):
        return rows
    nested = payload.get("triad_cocycle_floor_rows")
    if not isinstance(nested, list):
        return []
    flat: list[dict[str, Any]] = []
    for frame_row in nested:
        if not isinstance(frame_row, dict):
            continue
        frame = frame_row.get("frame")
        shell_rows = frame_row.get("shell_rows")
        if isinstance(shell_rows, list):
            for shell_row in shell_rows:
                if isinstance(shell_row, dict):
                    row = dict(shell_row)
                    row.setdefault("frame", frame)
                    flat.append(row)
    return flat


def _key(row: dict[str, Any]) -> tuple[int, int] | None:
    frame = row.get("frame")
    shell = row.get("shell", row.get("shell_n"))
    if not isinstance(frame, int) or not isinstance(shell, int):
        return None
    return frame, shell


def _mean(values: list[float]) -> float:
    return float(sum(values) / len(values)) if values else 0.0


def _safe_float(value: Any, default: float = 0.0) -> float:
    if value is None or isinstance(value, bool):
        return default
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return default
    return parsed if math.isfinite(parsed) else default


def main() -> int:
    args = _parse_args()
    gauge = _read_json(args.gaugeability_json)
    spectral = _read_json(args.spectral_json)
    cocycle = _read_json(args.cocycle_json)
    schur = _read_json(args.schur_json)

    by_key: dict[tuple[int, int], dict[str, Any]] = {}
    for row in _rows(gauge):
        if isinstance(row, dict):
            k = _key(row)
            if k is not None:
                by_key.setdefault(k, {}).update({"gauge": row})
    for row in _rows(spectral):
        if isinstance(row, dict):
            k = _key(row)
            if k is not None:
                by_key.setdefault(k, {}).update({"spectral": row})
    for row in _cocycle_rows(cocycle):
        if isinstance(row, dict):
            k = _key(row)
            if k is not None:
                by_key.setdefault(k, {}).update({"cocycle": row})
    for row in _rows(schur):
        if isinstance(row, dict):
            k = _key(row)
            if k is not None:
                by_key.setdefault(k, {}).update({"schur": row})

    summary_rows: list[dict[str, Any]] = []
    for (frame, shell), payloads in sorted(by_key.items()):
        if set(payloads) != {"gauge", "spectral", "cocycle", "schur"}:
            continue
        g = payloads["gauge"]
        s = payloads["spectral"]
        c = payloads["cocycle"]
        h = payloads["schur"]
        gauge_fields = (
            "psi_pi_weight_fraction",
            "signed_xor_weighted_distance_fraction",
            "signed_xor_distance_vs_balance_capacity",
        )
        spectral_fields = (
            "xy_floor_spectral_lower_bound",
            "signed_laplacian_lambda_min",
            "signed_laplacian_lambda_max",
            "signed_frame_gap_from_l",
            "identity_error_op",
        )
        if any(field not in g for field in gauge_fields):
            continue
        if any(field not in s for field in spectral_fields):
            continue
        summary_rows.append(
            {
                "frame": frame,
                "shell": shell,
                "status": "ok",
                "psi_pi_fraction": float(g["psi_pi_weight_fraction"]),
                "signed_xor_distance_fraction": float(g["signed_xor_weighted_distance_fraction"]),
                "signed_xor_distance_vs_balance_capacity": float(g["signed_xor_distance_vs_balance_capacity"]),
                "observed_floor_ratio": float(c.get("frustration_floor_ratio_vs_raw", 0.0)),
                "observed_floor_proxy": float(c.get("frustration_floor_proxy", 0.0)),
                "spectral_floor_lower_bound": float(s["xy_floor_spectral_lower_bound"]),
                "signed_laplacian_lambda_min": float(s["signed_laplacian_lambda_min"]),
                "signed_laplacian_lambda_max": float(s["signed_laplacian_lambda_max"]),
                "signed_frame_gap_lower_edge": float(s["signed_frame_gap_from_l"]),
                "signed_frame_gap_k_proxy": float(s["signed_frame_gap_from_k"]),
                "identity_error_op": float(s["identity_error_op"]),
                "schur_gap": _safe_float(h.get("schur_min_eigenvalue"), 0.0),
                "schur_directional_gap_proxy": _safe_float(h.get("schur_directional_gap_proxy"), 0.0),
            }
        )

    aggregate = {
        "shared_frame_shell_count": len(summary_rows),
        "psi_pi_fraction_mean": _mean([row["psi_pi_fraction"] for row in summary_rows]),
        "signed_xor_distance_fraction_mean": _mean([row["signed_xor_distance_fraction"] for row in summary_rows]),
        "signed_xor_distance_vs_balance_capacity_mean": _mean(
            [row["signed_xor_distance_vs_balance_capacity"] for row in summary_rows]
        ),
        "observed_floor_ratio_mean": _mean([row["observed_floor_ratio"] for row in summary_rows]),
        "spectral_floor_lower_bound_mean": _mean([row["spectral_floor_lower_bound"] for row in summary_rows]),
        "signed_frame_gap_lower_edge_mean": _mean([row["signed_frame_gap_lower_edge"] for row in summary_rows]),
        "schur_gap_mean": _mean([row["schur_gap"] for row in summary_rows]),
        "identity_error_op_mean": _mean([row["identity_error_op"] for row in summary_rows]),
        "wall1a_status": "unproved",
        "wall1b_status": "unproved",
    }

    signed_wall1_rows = [
        {
            "surface": "signed_xor_gaugeability",
            "module_path": "DASHI/Physics/Closure/NSTriadSignedXORGaugeabilityBoundary.agda",
            "receipt_name": "NSTriadSignedXORGaugeabilityBoundary",
            "route_name": "wall1a-signed-xor-gaugeability",
            "boundary_summary": (
                "Sign balance does not imply frustration; gaugeable signed XOR is satisfiable; the non-gaugeable signed XOR obstruction surface remains empirical."
            ),
            "bridge_summary": (
                "The weighted-distance bridge to gaugeability remains open; d_W(b, im B₂) is the quantitative target."
            ),
            "candidate_only": True,
            "fail_closed": True,
            "theorem_promoted": False,
            "full_ns_promoted": False,
            "clay_promoted": False,
            "wall1_status": "unproved",
            "weighted_distance_target_text": "d_W(b, im B₂)",
            "gaugeable_signed_xor_satisfiable": True,
            "non_gaugeable_signed_xor_is_actual_obstruction_surface": True,
            "signed_xor_bridge_open": True,
        },
        {
            "surface": "signed_spectral_frustration",
            "module_path": "DASHI/Physics/Closure/NSTriadSignedSpectralFrustrationBoundary.agda",
            "receipt_name": "NSTriadSignedSpectralFrustrationBoundary",
            "route_name": "signed-XY-spectral-frustration-wall-1a",
            "boundary_summary": (
                "Signed Laplacian / signed XY floor candidate remains open, upper spectral edge still carries XY-floor risk, and theorem/full-NS/Clay promotion stays false."
            ),
            "bridge_summary": (
                "The discrete signed-XOR distance to the continuous XY floor bridge is still open."
            ),
            "candidate_only": True,
            "fail_closed": True,
            "theorem_promoted": False,
            "full_ns_promoted": False,
            "clay_promoted": False,
            "wall1_status": "unproved",
            "primary_wall1a_candidate": True,
            "upper_spectral_edge_carries_xy_floor_risk": True,
            "signed_xor_distance_bridge_open": True,
        },
    ]

    aggregate.update(
        {
            "signed_wall1_row_count": len(signed_wall1_rows),
            "signed_wall1_surface_count": len({row["surface"] for row in signed_wall1_rows}),
            "signed_wall1_status": "fail-closed",
            "signed_surface_consensus": "fail-closed",
            "signed_wall1_candidate_only": True,
            "signed_wall1_fail_closed": True,
            "signed_wall1_theorem_promoted": False,
            "signed_wall1_full_ns_promoted": False,
            "signed_wall1_clay_promoted": False,
            "signed_xor_bridge_open": True,
            "signed_spectral_bridge_open": True,
            "signed_wall1_route_names": [row["route_name"] for row in signed_wall1_rows],
        }
    )

    out = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "candidate_only": True,
        "empirical_non_promoting": True,
        "fail_closed": True,
        "theorem_authority": False,
        "clay_authority": False,
        "rows": summary_rows,
        "signed_wall1_rows": signed_wall1_rows,
        "aggregate": aggregate,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(out, pretty=args.pretty), encoding="utf-8")
    args.output_csv.parent.mkdir(parents=True, exist_ok=True)
    with args.output_csv.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "frame",
                "shell",
                "status",
                "psi_pi_fraction",
                "signed_xor_distance_fraction",
                "signed_xor_distance_vs_balance_capacity",
                "observed_floor_ratio",
                "observed_floor_proxy",
                "spectral_floor_lower_bound",
                "signed_laplacian_lambda_min",
                "signed_laplacian_lambda_max",
                "signed_frame_gap_lower_edge",
                "signed_frame_gap_k_proxy",
                "identity_error_op",
                "schur_gap",
                "schur_directional_gap_proxy",
            ],
        )
        writer.writeheader()
        writer.writerows(summary_rows)
    print(_json_text(out, pretty=args.pretty))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
