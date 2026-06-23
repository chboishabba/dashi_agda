#!/usr/bin/env python3
"""Validate ns_triad_kn_tail_progression_scan output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_triad_kn_tail_progression_scan.py"
CONTRACT = "check_ns_triad_kn_tail_progression_scan"
SOURCE_CONTRACT = "ns_triad_kn_tail_progression_scan"
SOURCE_SCRIPT_NAME = "scripts/ns_triad_kn_tail_progression_scan.py"
SOURCE_ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_TAIL_PROGRESSION_SCAN"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_TAIL_PROGRESSION_SCAN_CHECK"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"
BACKENDS = {"cpu-matrix-free", "vulkan-matvec"}
BRANCHES = {
    "frame-coercive",
    "low-radial-band",
    "finite-low-shell-degeneracy",
    "asymptotic-tail-danger",
    "high-dissipation",
    "partial",
    "unavailable",
}

DEFAULT_SOURCE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_tail_progression_scan_N128_20260623.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "check_ns_triad_kn_tail_progression_scan_N128_20260623.json"
)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source_json", nargs="?", type=Path)
    parser.add_argument("--source-json", type=Path, dest="source_json_kw")
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _input_path(args: argparse.Namespace) -> Path:
    if args.source_json is not None and args.source_json_kw is not None:
        raise ValueError("provide either positional source_json or --source-json, not both")
    if args.source_json is None and args.source_json_kw is None:
        return DEFAULT_SOURCE_JSON
    return args.source_json if args.source_json is not None else args.source_json_kw


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("payload must be object")
    return payload


def _finite_or_none(value: Any) -> float | None:
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
    if isinstance(value, int) and value >= 0:
        return value
    if isinstance(value, float) and math.isfinite(value) and value.is_integer() and value >= 0.0:
        return int(value)
    return None


def _check_tail_grid(profile: dict[str, Any], path: str, errors: list[str]) -> None:
    summary = profile.get("tail_grid_summary")
    grid = profile.get("tail_grid")
    if not isinstance(summary, dict):
        errors.append(f"{path}.tail_grid_summary: must be object")
    if not isinstance(grid, list) or not grid:
        errors.append(f"{path}.tail_grid: must be non-empty list")
        return
    for index, item in enumerate(grid[:20]):
        if not isinstance(item, dict):
            errors.append(f"{path}.tail_grid[{index}]: must be object")
            continue
        for key in ("c0", "tail_eta", "d0", "high_shell_mass_k"):
            if _finite_or_none(item.get(key)) is None:
                errors.append(f"{path}.tail_grid[{index}].{key}: must be finite")
        if _nonnegative_int(item.get("tail_cutoff")) is None:
            errors.append(f"{path}.tail_grid[{index}].tail_cutoff: must be nonnegative int")
        if item.get("branch") not in BRANCHES:
            errors.append(f"{path}.tail_grid[{index}].branch: invalid")


def _check_profile(profile: Any, path: str, backend: str, errors: list[str]) -> None:
    if profile is None:
        return
    if not isinstance(profile, dict):
        errors.append(f"{path}: must be object or null")
        return
    if profile.get("kn_backend") != backend:
        errors.append(f"{path}.kn_backend: must match row backend")
    for key in ("candidate_only", "fail_closed"):
        if profile.get(key) is not True:
            errors.append(f"{path}.{key}: must be true")
    if profile.get("gpu_kn_authority") is not False:
        errors.append(f"{path}.gpu_kn_authority: must be false")
    if profile.get("dense_reconstruction_used") is not False:
        errors.append(f"{path}.dense_reconstruction_used: must be false")
    if profile.get("block_matvec_enabled") is not True:
        errors.append(f"{path}.block_matvec_enabled: must be true")
    if profile.get("block_matvec_backend") not in {"cpu-column-loop", "vulkan-csr-block"}:
        errors.append(f"{path}.block_matvec_backend: invalid")
    if not isinstance(profile.get("parity_ok"), bool):
        errors.append(f"{path}.parity_ok: must be bool")
    for key in ("lambda_min_iterative", "worst_eigenvector_shell_mass_iterative", "residual_norm", "elapsed_ms"):
        if _finite_or_none(profile.get(key)) is None:
            errors.append(f"{path}.{key}: must be finite")
    if not isinstance(profile.get("metrics"), dict):
        errors.append(f"{path}.metrics: must be object")
    _check_tail_grid(profile, path, errors)
    if backend == "vulkan-matvec":
        if profile.get("gpu_matvec_parity_ok") is not True:
            errors.append(f"{path}.gpu_matvec_parity_ok: must be true for vulkan backend")
        if profile.get("gpu_block_matvec_parity_ok") is not True:
            errors.append(f"{path}.gpu_block_matvec_parity_ok: must be true for vulkan backend")


def main() -> int:
    args = _parse_args()
    source_json = _input_path(args)
    payload = _load_json(source_json)
    errors: list[str] = []

    if payload.get("contract") != SOURCE_CONTRACT:
        errors.append(f"contract: must be {SOURCE_CONTRACT!r}")
    if payload.get("route_decision") != SOURCE_ROUTE_DECISION:
        errors.append(f"route_decision: must be {SOURCE_ROUTE_DECISION!r}")
    if payload.get("script_name") != SOURCE_SCRIPT_NAME:
        errors.append(f"script_name: must be {SOURCE_SCRIPT_NAME!r}")

    parameters = payload.get("parameters")
    backend = parameters.get("kn_backend") if isinstance(parameters, dict) else None
    if backend not in BACKENDS:
        errors.append("parameters.kn_backend: invalid")
        backend = "cpu-matrix-free"

    rows = payload.get("rows")
    if not isinstance(rows, list) or not rows:
        errors.append("rows: must be non-empty list")
        rows = []
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            errors.append(f"rows[{index}]: must be object")
            continue
        if row.get("status") not in {OK_STATUS, PARTIAL_STATUS, ERROR_STATUS}:
            errors.append(f"rows[{index}].status: invalid")
        if row.get("kn_backend") != backend:
            errors.append(f"rows[{index}].kn_backend: must match parameters.kn_backend")
        if row.get("gpu_kn_authority") is not False:
            errors.append(f"rows[{index}].gpu_kn_authority: must be false")
        if row.get("dense_reconstruction_used") is not False:
            errors.append(f"rows[{index}].dense_reconstruction_used: must be false")
        for key in ("candidate_only", "fail_closed"):
            if row.get(key) is not True:
                errors.append(f"rows[{index}].{key}: must be true")
        for key in (
            "frame",
            "snapshot_index",
            "shell",
            "selected_mode_count",
            "triad_count",
            "profile_count",
            "parity_ok_count",
            "parity_mismatch_count",
            "asymptotic_tail_candidate_count",
        ):
            if row.get(key) is not None and _nonnegative_int(row.get(key)) is None:
                errors.append(f"rows[{index}].{key}: must be nonnegative int")
        _check_profile(row.get("best_profile"), f"rows[{index}].best_profile", str(backend), errors)
        samples = row.get("profile_samples")
        if samples is not None:
            if not isinstance(samples, list):
                errors.append(f"rows[{index}].profile_samples: must be list")
            else:
                for sample_index, sample in enumerate(samples[:5]):
                    _check_profile(sample, f"rows[{index}].profile_samples[{sample_index}]", str(backend), errors)

    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        errors.append("aggregate: must be object")
    else:
        if aggregate.get("kn_backend") != backend:
            errors.append("aggregate.kn_backend: must match parameters.kn_backend")
        for key in ("candidate_only", "fail_closed"):
            if aggregate.get(key) is not True:
                errors.append(f"aggregate.{key}: must be true")
        for key in ("gpu_kn_authority", "theorem_promoted", "full_ns_promoted", "clay_promoted"):
            if aggregate.get(key) is not False:
                errors.append(f"aggregate.{key}: must be false")
        if aggregate.get("dense_eigensolve_scope") != "small_shell_oracle_only":
            errors.append("aggregate.dense_eigensolve_scope: invalid")
        if aggregate.get("dense_reconstruction_used_by_iterative_lane") is not False:
            errors.append("aggregate.dense_reconstruction_used_by_iterative_lane: must be false")
        for key in (
            "processed_rows",
            "ok_rows",
            "partial_rows",
            "error_rows",
            "sampled_profile_count",
            "parity_mismatch_count",
            "asymptotic_tail_candidate_count",
        ):
            if _nonnegative_int(aggregate.get(key)) is None:
                errors.append(f"aggregate.{key}: must be nonnegative int")

    receipt = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "source_json": str(source_json),
        "source_contract": SOURCE_CONTRACT,
        "source_script_name": SOURCE_SCRIPT_NAME,
        "status": OK_STATUS if not errors else ERROR_STATUS,
        "ok": not errors,
        "error_count": int(len(errors)),
        "errors": errors,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(receipt, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(receipt, args.pretty))
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
