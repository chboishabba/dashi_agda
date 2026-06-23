#!/usr/bin/env python3
"""Validate constrained adversarial fork optimizer output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_triad_constrained_adversarial_fork_optimizer.py"
CONTRACT = "check_ns_triad_constrained_adversarial_fork_optimizer"
SOURCE_CONTRACT = "ns_triad_constrained_adversarial_fork_optimizer"
SOURCE_SCRIPT_NAME = "scripts/ns_triad_constrained_adversarial_fork_optimizer.py"
SOURCE_ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_CONSTRAINED_ADVERSARIAL_FORK_OPTIMIZER"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_CONSTRAINED_ADVERSARIAL_FORK_OPTIMIZER_CHECK"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"

DEFAULT_SOURCE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_constrained_adversarial_fork_optimizer_N128_20260623.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "check_ns_triad_constrained_adversarial_fork_optimizer_N128_20260623.json"
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


def _finite(value: Any) -> float | None:
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


def _check_profile(profile: Any, path: str, errors: list[str]) -> None:
    if profile is None:
        return
    if not isinstance(profile, dict):
        errors.append(f"{path}: must be object or null")
        return
    for key in (
        "lambda_min_kn_a",
        "lambda_max_kn_a",
        "energy",
        "n_eff",
        "angular_entropy",
        "radial_shell_min",
        "radial_shell_max",
        "radial_shell_barycenter",
        "radial_shell_variance",
        "radial_effective_scale",
        "high_shell_mass_fraction",
        "dissipation_proxy",
        "bkm_proxy",
        "product_separation_lambda_min_times_n_eff_5_over_2",
    ):
        if _finite(profile.get(key)) is None:
            errors.append(f"{path}.{key}: must be finite")
    if _nonnegative_int(profile.get("angular_mode_count")) is None:
        errors.append(f"{path}.angular_mode_count: must be nonnegative int")
    if profile.get("branch") not in {"frame-coercive", "low-radial-band", "high-dissipation", "unresolved-danger", "unavailable"}:
        errors.append(f"{path}.branch: invalid")
    for key in ("feasible_constraint", "old_angular_feasible_constraint", "angular_multiplicity_artifact", "triple_danger"):
        if not isinstance(profile.get(key), bool):
            errors.append(f"{path}.{key}: must be bool")
    if _nonnegative_int(profile.get("l_abs_positive_rank")) is None:
        errors.append(f"{path}.l_abs_positive_rank: must be nonnegative int")


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
        for key in (
            "frame",
            "snapshot_index",
            "shell",
            "profile_count",
            "ok_profile_count",
            "feasible_profile_count",
            "triple_danger_count",
            "angular_multiplicity_artifact_count",
        ):
            if row.get(key) is not None and _nonnegative_int(row.get(key)) is None:
                errors.append(f"rows[{index}].{key}: must be nonnegative int")
        _check_profile(row.get("best_feasible_profile"), f"rows[{index}].best_feasible_profile", errors)
        _check_profile(row.get("best_any_profile"), f"rows[{index}].best_any_profile", errors)
        samples = row.get("profile_samples")
        if samples is not None:
            if not isinstance(samples, list):
                errors.append(f"rows[{index}].profile_samples: must be list")
            else:
                for sample_index, sample in enumerate(samples[:5]):
                    _check_profile(sample, f"rows[{index}].profile_samples[{sample_index}]", errors)

    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        errors.append("aggregate: must be object")
    else:
        if aggregate.get("constrained_adversarial_fork_status") != "fail-closed":
            errors.append("aggregate.constrained_adversarial_fork_status: must be fail-closed")
        if aggregate.get("bandwidth_variable_status") != "corrected_to_radial_diagnostic":
            errors.append("aggregate.bandwidth_variable_status: must be corrected_to_radial_diagnostic")
        if aggregate.get("old_angular_n_eff_status") != "diagnostic_only_not_radial_bandwidth":
            errors.append("aggregate.old_angular_n_eff_status: must be diagnostic_only_not_radial_bandwidth")
        for key in ("candidate_only", "fail_closed"):
            if aggregate.get(key) is not True:
                errors.append(f"aggregate.{key}: must be true")
        for key in ("theorem_promoted", "full_ns_promoted", "clay_promoted"):
            if aggregate.get(key) is not False:
                errors.append(f"aggregate.{key}: must be false")
        if aggregate.get("wall1a_status") != "unproved":
            errors.append("aggregate.wall1a_status: must be unproved")
        for key in (
            "processed_rows",
            "ok_rows",
            "sampled_profile_count",
            "feasible_profile_count",
            "triple_danger_count",
            "angular_multiplicity_artifact_count",
        ):
            if _nonnegative_int(aggregate.get(key)) is None:
                errors.append(f"aggregate.{key}: must be nonnegative int")
        _check_profile(aggregate.get("best_global_feasible_profile"), "aggregate.best_global_feasible_profile", errors)

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
