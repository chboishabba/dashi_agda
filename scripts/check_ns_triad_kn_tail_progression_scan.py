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
EIGENMODE_TAIL_PREFIXES = ("eigen_tail_", "eigenmode_tail_", "eigenvector_tail_")

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


def _branch_label(payload: dict[str, Any]) -> str | None:
    branch = payload.get("branch")
    if isinstance(branch, str):
        return branch
    branch = payload.get("branch_classification_iterative")
    if isinstance(branch, str):
        return branch
    return None


def _check_optional_eigenmode_tail_telemetry(
    payload: dict[str, Any], path: str, errors: list[str], branch: str | None = None
) -> None:
    tail_keys = [
        key
        for key in payload
        if key.startswith(EIGENMODE_TAIL_PREFIXES)
        or key in {
            "worst_eigenvector_shell_finite",
            "worst_eigenvector_shell_is_finite",
        }
    ]
    if not tail_keys:
        return

    for key in tail_keys:
        value = payload.get(key)
        if value is None:
            continue
        if isinstance(value, dict):
            for nested_key, nested_value in value.items():
                if nested_value is None:
                    continue
                if "mass" in key or "fraction" in key:
                    numeric = _finite_or_none(nested_value)
                    if numeric is None:
                        errors.append(f"{path}.{key}.{nested_key}: must be finite or null when present")
                    elif numeric < 0.0:
                        errors.append(f"{path}.{key}.{nested_key}: must be nonnegative when present")
                elif "shell" in key and _nonnegative_int(nested_value) is None:
                    errors.append(f"{path}.{key}.{nested_key}: must be nonnegative int or null when present")
            continue
        if key.endswith(("_present", "_absent", "_finite", "_is_finite")):
            if not isinstance(value, bool):
                errors.append(f"{path}.{key}: must be bool when present")
            continue
        if "mass" in key or "fraction" in key:
            numeric = _finite_or_none(value)
            if numeric is None:
                errors.append(f"{path}.{key}: must be finite when present")
                continue
            if numeric < 0.0:
                errors.append(f"{path}.{key}: must be nonnegative when present")
            continue
        if "shell" in key:
            if _nonnegative_int(value) is None:
                errors.append(f"{path}.{key}: must be nonnegative int when present")
            continue
        if "count" in key:
            if _nonnegative_int(value) is None:
                errors.append(f"{path}.{key}: must be nonnegative int when present")
            continue

    branch = _branch_label(payload) if branch is None else branch
    if branch != "asymptotic-tail-danger":
        return

    mass_keys = [key for key in tail_keys if "mass" in key or "fraction" in key]
    finite_mass_keys = [key for key in mass_keys if _finite_or_none(payload.get(key)) is not None]
    absent_mass_keys = [key for key in mass_keys if payload.get(key) is None]
    if not finite_mass_keys:
        errors.append(f"{path}: asymptotic-tail-danger requires finite eigenmode-tail mass telemetry")
    for key in tail_keys:
        if key.endswith("_absent") and payload.get(key) is True:
            errors.append(f"{path}.{key}: must be false for asymptotic-tail-danger")
        if key.endswith(("_present", "_finite", "_is_finite")) and payload.get(key) is False:
            errors.append(f"{path}.{key}: must be true for asymptotic-tail-danger")
    if absent_mass_keys and len(absent_mass_keys) == len(mass_keys):
        errors.append(f"{path}: asymptotic-tail-danger cannot be reported with absent eigenmode-tail mass")


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
        _check_optional_eigenmode_tail_telemetry(
            item,
            f"{path}.tail_grid[{index}]",
            errors,
            branch=str(item.get("branch")) if isinstance(item.get("branch"), str) else None,
        )
    if isinstance(summary, dict):
        branch_counts = summary.get("branch_counts")
        if isinstance(branch_counts, dict):
            counted = sum(
                int(branch_counts.get(branch, 0))
                for branch in (
                    "frame-coercive",
                    "low-radial-band",
                    "finite-low-shell-degeneracy",
                    "asymptotic-tail-danger",
                    "high-dissipation",
                    "partial",
                    "unavailable",
                )
            )
            if _nonnegative_int(summary.get("grid_point_count")) is not None and counted != int(summary["grid_point_count"]):
                errors.append(f"{path}.tail_grid_summary.branch_counts: must sum to grid_point_count")
        _check_optional_eigenmode_tail_telemetry(summary, f"{path}.tail_grid_summary", errors, branch=_branch_label(profile))


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
    _check_optional_eigenmode_tail_telemetry(profile, path, errors)
    _check_optional_eigenmode_tail_telemetry(
        profile.get("metrics") if isinstance(profile.get("metrics"), dict) else {},
        f"{path}.metrics",
        errors,
        branch=_branch_label(profile),
    )
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
        _check_optional_eigenmode_tail_telemetry(row, f"rows[{index}]", errors)
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
