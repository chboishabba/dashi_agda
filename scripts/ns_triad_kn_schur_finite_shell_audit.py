#!/usr/bin/env python3
"""Finite-shell Schur-style audit surface for NS triad tail-scan receipts.

This script is intentionally candidate-only and non-promoting.  It reads one or
more tail-scan JSON receipts, looks for explicit finite-low-shell-degeneracy
examples when they are present, and otherwise falls back to conservative proxy
selection from the existing receipt fields.

Where exact Schur blocks are unavailable, the script reports q_diag/q_coup/q_gap
as proxy telemetry and labels the row partial.  The output is meant to help
prioritize exact Schur work, not to claim any theorem.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from statistics import mean
from typing import Any


SCRIPT_NAME = "scripts/ns_triad_kn_schur_finite_shell_audit.py"
CONTRACT = "ns_triad_kn_schur_finite_shell_audit"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_SCHUR_FINITE_SHELL_AUDIT"
SCHEMA_VERSION = "1.0.0"

DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_schur_finite_shell_audit_N128_20260623.json"
)
DEFAULT_INPUT_GLOB = "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_tail_progression_scan_*.json"

AUTHORITY = {
    "candidate_only": True,
    "empirical_non_promoting": True,
    "truth_authority": False,
    "theorem_authority": False,
    "clay_authority": False,
    "runtime_authority": False,
    "promoted": False,
}

CONTROL_CARD = {
    "O": "Surface finite-shell Schur-style audit telemetry from tail-scan receipts.",
    "R": (
        "Read candidate rows, select finite-low-shell-degeneracy examples, and report "
        "q_diag/q_coup/q_gap as exact or proxy telemetry from the receipt fields."
    ),
    "C": SCRIPT_NAME,
    "S": "Candidate-only telemetry; exact blocks are optional and missing blocks downgrade the row to partial.",
    "L": (
        "Load tail-scan JSON receipts, inspect top-level rows and nested best_profile/tail_grid records, "
        "score finite low-shell examples, and emit exact-or-proxy q telemetry."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, full-NS, or Clay promotion is inferred from this audit surface.",
    "F": "The audit prioritizes exact Schur work and does not claim a proof; partial and proxy rows remain explicitly flagged.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tail_jsons", nargs="*", type=Path, help="Tail-scan JSON receipts to audit.")
    parser.add_argument(
        "--tail-json",
        dest="tail_jsons_kw",
        action="append",
        type=Path,
        default=None,
        help="Tail-scan JSON receipt to audit; repeatable.",
    )
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--finite-shell-cutoff", type=int, default=4)
    parser.add_argument("--low-tail-mass-threshold", type=float, default=0.05)
    parser.add_argument("--max-selected", type=int, default=24)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _finite_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _nonnegative_int(value: Any) -> int | None:
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value if value >= 0 else None
    if isinstance(value, float) and math.isfinite(value) and value.is_integer() and value >= 0.0:
        return int(value)
    return None


def _load_json(path: Path) -> tuple[dict[str, Any] | None, list[str], list[str]]:
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


def _payload_rows(payload: dict[str, Any] | None) -> list[dict[str, Any]]:
    if not isinstance(payload, dict):
        return []
    for key in (
        "rows",
        "tail_rows",
        "tail_progression_rows",
        "scan_rows",
        "tail_scan_rows",
    ):
        value = payload.get(key)
        if isinstance(value, list):
            return [row for row in value if isinstance(row, dict)]
    return []


def _tail_grid_rows(profile: dict[str, Any] | None) -> list[dict[str, Any]]:
    if not isinstance(profile, dict):
        return []
    value = profile.get("tail_grid")
    if isinstance(value, list):
        return [row for row in value if isinstance(row, dict)]
    return []


def _tail_grid_summary(profile: dict[str, Any] | None) -> dict[str, Any]:
    if not isinstance(profile, dict):
        return {}
    value = profile.get("tail_grid_summary")
    return value if isinstance(value, dict) else {}


def _metrics_dict(profile: dict[str, Any] | None) -> dict[str, Any]:
    if not isinstance(profile, dict):
        return {}
    value = profile.get("metrics")
    return value if isinstance(value, dict) else {}


def _first_finite(*values: Any) -> float | None:
    for value in values:
        parsed = _finite_float(value)
        if parsed is not None:
            return parsed
    return None


def _normalize_branch(value: Any) -> str | None:
    if not isinstance(value, str):
        return None
    return value.strip()


def _branch_is_finite_low_shell(branch: str | None) -> bool:
    return branch in {"finite-low-shell-degeneracy", "finite_low_shell_degeneracy"}


def _selection_kind(
    *,
    row: dict[str, Any],
    profile: dict[str, Any] | None,
    tail_item: dict[str, Any] | None,
    finite_shell_cutoff: int,
    low_tail_mass_threshold: float,
) -> tuple[str | None, str, bool, bool]:
    branch = _normalize_branch((tail_item or {}).get("branch")) or _normalize_branch(row.get("branch"))
    explicit_exact = _branch_is_finite_low_shell(branch)
    if explicit_exact:
        return branch, "exact_finite_low_shell_degeneracy", True, False

    shell = _nonnegative_int(row.get("shell"))
    metrics = _metrics_dict(profile)
    radial_shell_max = _nonnegative_int(
        _first_finite(
            metrics.get("radial_shell_max"),
            profile.get("worst_eigenvector_shell_iterative") if isinstance(profile, dict) else None,
            row.get("shell"),
        )
    )
    high_tail_mass = _first_finite(
        (tail_item or {}).get("high_shell_mass_k"),
        metrics.get("high_shell_mass_fraction"),
        metrics.get("high_shell_mass_by_cutoff", {}).get(str(shell)) if shell is not None else None,
    )
    low_shell_like = any(
        candidate is not None and int(candidate) <= int(finite_shell_cutoff)
        for candidate in (shell, radial_shell_max)
    )
    low_tail_like = high_tail_mass is not None and float(high_tail_mass) <= float(low_tail_mass_threshold)
    if low_shell_like and low_tail_like:
        return branch, "proxy_finite_low_shell_degeneracy", False, True
    return branch, "not_selected", False, False


def _proxy_telemetry(
    *,
    row: dict[str, Any],
    profile: dict[str, Any] | None,
    tail_item: dict[str, Any] | None,
) -> dict[str, Any]:
    metrics = _metrics_dict(profile)
    diag_exact = _first_finite(
        row.get("q_diag"),
        (profile or {}).get("q_diag") if isinstance(profile, dict) else None,
    )
    coup_exact = _first_finite(
        row.get("q_coup"),
        (profile or {}).get("q_coup") if isinstance(profile, dict) else None,
    )
    gap_exact = _first_finite(
        row.get("q_gap"),
        (profile or {}).get("q_gap") if isinstance(profile, dict) else None,
    )

    diag_proxy_source = None
    diag_proxy = None
    for source_name, value in (
        ("exact:q_diag", diag_exact),
        ("profile.lambda_min_iterative", _first_finite(metrics.get("lambda_min_iterative"), (profile or {}).get("lambda_min_iterative"))),
        ("profile.lambda_min_dense_cpu", _first_finite(metrics.get("lambda_min_dense_cpu"), (profile or {}).get("lambda_min_dense_cpu"))),
        ("profile.radial_effective_scale", _first_finite(metrics.get("radial_effective_scale"))),
        ("profile.frame_stability_margin_proxy", _first_finite(row.get("frame_stability_margin_proxy"))),
    ):
        if value is not None:
            diag_proxy = float(value)
            diag_proxy_source = source_name
            break

    coup_proxy_source = None
    coup_proxy = None
    tail_mass = _first_finite(
        (tail_item or {}).get("high_shell_mass_k"),
        metrics.get("high_shell_mass_fraction"),
        metrics.get("high_shell_mass_by_cutoff", {}).get(str(_nonnegative_int(row.get("shell")) or 0)),
        metrics.get("worst_eigenvector_shell_mass_iterative"),
        row.get("dangerous_subspace_weight_fraction"),
        row.get("k01_operator_norm"),
        row.get("residual_norm"),
    )
    for source_name, value in (
        ("exact:q_coup", coup_exact),
        ("tail_grid.high_shell_mass_k", _first_finite((tail_item or {}).get("high_shell_mass_k"))),
        ("profile.high_shell_mass_fraction", _first_finite(metrics.get("high_shell_mass_fraction"))),
        ("profile.worst_eigenvector_shell_mass_iterative", _first_finite(row.get("worst_eigenvector_shell_mass_iterative"))),
        ("profile.dangerous_subspace_weight_fraction", _first_finite(row.get("dangerous_subspace_weight_fraction"))),
        ("profile.k01_operator_norm", _first_finite(row.get("k01_operator_norm"))),
        ("profile.residual_norm", _first_finite(row.get("residual_norm"))),
    ):
        if value is not None:
            coup_proxy = float(value)
            coup_proxy_source = source_name
            break

    gap_proxy_source = None
    gap_proxy = None
    if gap_exact is not None:
        gap_proxy = float(gap_exact)
        gap_proxy_source = "exact:q_gap"
    elif diag_proxy is not None and coup_proxy is not None:
        gap_proxy = float(diag_proxy - coup_proxy)
        gap_proxy_source = "derived:q_diag_minus_q_coup"
    else:
        for source_name, value in (
            ("profile.schur_directional_gap_proxy", _first_finite(row.get("schur_directional_gap_proxy"))),
            ("profile.directional_gap_proxy", _first_finite(row.get("directional_gap_proxy"))),
            ("profile.optimized_lambda_gap_proxy", _first_finite(row.get("optimized_lambda_gap_proxy"))),
        ):
            if value is not None:
                gap_proxy = float(value)
                gap_proxy_source = source_name
                break

    exact_available = diag_exact is not None and coup_exact is not None and gap_exact is not None
    telemetry_status = "exact" if exact_available else "partial"
    if diag_proxy is None or coup_proxy is None or gap_proxy is None:
        telemetry_status = "partial"

    return {
        "q_diag_exact": diag_exact,
        "q_coup_exact": coup_exact,
        "q_gap_exact": gap_exact,
        "q_diag_proxy": diag_proxy,
        "q_diag_proxy_source": diag_proxy_source,
        "q_coup_proxy": coup_proxy,
        "q_coup_proxy_source": coup_proxy_source,
        "q_gap_proxy": gap_proxy,
        "q_gap_proxy_source": gap_proxy_source,
        "q_gap_proxy_residual": None if gap_proxy is None or diag_proxy is None or coup_proxy is None else float(
            gap_proxy - (diag_proxy - coup_proxy)
        ),
        "exact_blocks_available": exact_available,
        "telemetry_status": telemetry_status,
        "tail_mass_proxy": tail_mass,
    }


def _selected_example(
    *,
    source_json: Path,
    row_index: int,
    row: dict[str, Any],
    profile: dict[str, Any] | None,
    tail_item: dict[str, Any] | None,
    tail_item_index: int | None,
    finite_shell_cutoff: int,
    low_tail_mass_threshold: float,
) -> dict[str, Any] | None:
    branch, selection_kind, exact_branch, proxy_branch = _selection_kind(
        row=row,
        profile=profile,
        tail_item=tail_item,
        finite_shell_cutoff=finite_shell_cutoff,
        low_tail_mass_threshold=low_tail_mass_threshold,
    )
    if selection_kind == "not_selected":
        return None

    metrics = _metrics_dict(profile)
    tail_summary = _tail_grid_summary(profile)
    telemetry = _proxy_telemetry(row=row, profile=profile, tail_item=tail_item)
    shell = _nonnegative_int(row.get("shell"))
    snapshot_index = _nonnegative_int(row.get("snapshot_index"))
    frame = _nonnegative_int(row.get("frame"))
    high_shell_mass_fraction = _first_finite(
        (tail_item or {}).get("high_shell_mass_k"),
        metrics.get("high_shell_mass_fraction"),
    )
    radial_shell_max = _first_finite(
        metrics.get("radial_shell_max"),
        profile.get("worst_eigenvector_shell_iterative") if isinstance(profile, dict) else None,
        shell,
    )
    worst_shell_mass = _first_finite(profile.get("worst_eigenvector_shell_mass_iterative") if isinstance(profile, dict) else None)
    selected = {
        "source_json": str(source_json),
        "row_index": int(row_index),
        "record_kind": "tail_grid" if tail_item is not None else "row",
        "tail_item_index": tail_item_index,
        "frame": frame,
        "snapshot_index": snapshot_index,
        "shell": shell,
        "branch": branch,
        "selection_kind": selection_kind,
        "candidate_only": True,
        "empirical_non_promoting": True,
        "fail_closed": True,
        "exact_branch": exact_branch,
        "proxy_branch": proxy_branch,
        "exact_blocks_available": telemetry["exact_blocks_available"],
        "telemetry_status": telemetry["telemetry_status"],
        "selection_status": "exact" if exact_branch else "partial",
        "tail_grid_summary": {
            "grid_point_count": _nonnegative_int(tail_summary.get("grid_point_count")),
            "finite_low_shell_degeneracy_count": _nonnegative_int(tail_summary.get("finite_low_shell_degeneracy_count")),
            "branch_counts": tail_summary.get("branch_counts") if isinstance(tail_summary.get("branch_counts"), dict) else {},
        },
        "tail_cutoff": _nonnegative_int((tail_item or {}).get("tail_cutoff")),
        "tail_eta": _first_finite((tail_item or {}).get("tail_eta")),
        "c0": _first_finite((tail_item or {}).get("c0")),
        "d0": _first_finite((tail_item or {}).get("d0")),
        "high_shell_mass_k": _first_finite((tail_item or {}).get("high_shell_mass_k")),
        "selected_mode_count": _nonnegative_int(row.get("selected_mode_count")),
        "triad_count": _nonnegative_int(row.get("triad_count")),
        "carrier_stratum_count": _nonnegative_int(row.get("carrier_stratum_count")),
        "lambda_min_iterative": _first_finite(
            telemetry["q_diag_exact"],
            telemetry["q_diag_proxy"],
            metrics.get("lambda_min_iterative"),
            (profile or {}).get("lambda_min_iterative") if isinstance(profile, dict) else None,
        ),
        "worst_eigenvector_shell_mass_iterative": worst_shell_mass,
        "radial_shell_max": radial_shell_max,
        "high_shell_mass_fraction": high_shell_mass_fraction,
        "tail_mass_proxy": telemetry["tail_mass_proxy"],
        "q_diag_exact": telemetry["q_diag_exact"],
        "q_coup_exact": telemetry["q_coup_exact"],
        "q_gap_exact": telemetry["q_gap_exact"],
        "q_diag_proxy": telemetry["q_diag_proxy"],
        "q_diag_proxy_source": telemetry["q_diag_proxy_source"],
        "q_coup_proxy": telemetry["q_coup_proxy"],
        "q_coup_proxy_source": telemetry["q_coup_proxy_source"],
        "q_gap_proxy": telemetry["q_gap_proxy"],
        "q_gap_proxy_source": telemetry["q_gap_proxy_source"],
        "q_gap_proxy_residual": telemetry["q_gap_proxy_residual"],
        "priority_score": None,
        "selection_reason": (
            "explicit finite-low-shell-degeneracy branch"
            if exact_branch
            else "finite-shell heuristic with small tail mass and low-shell carrier"
        ),
        "warnings": [
            "exact Schur blocks not materialized; q fields are proxy telemetry"
            if not telemetry["exact_blocks_available"]
            else "exact q telemetry present; still candidate-only"
        ],
    }

    q_diag_proxy = selected["q_diag_proxy"]
    q_coup_proxy = selected["q_coup_proxy"]
    if q_diag_proxy is not None and q_coup_proxy is not None:
        selected["priority_score"] = float(q_coup_proxy - q_diag_proxy)
    return selected


def _mean_or_none(values: list[float]) -> float | None:
    return float(mean(values)) if values else None


def _load_inputs(args: argparse.Namespace) -> tuple[list[Path], list[str], list[str]]:
    warnings: list[str] = []
    errors: list[str] = []
    inputs: list[Path] = []
    cli_inputs: list[Path] = []
    if isinstance(args.tail_jsons_kw, list):
        cli_inputs.extend(args.tail_jsons_kw)
    cli_inputs.extend(args.tail_jsons)
    if cli_inputs:
        inputs.extend(cli_inputs)
    else:
        inputs.extend(sorted(Path().glob(DEFAULT_INPUT_GLOB)))
        if not inputs:
            warnings.append(f"no default tail receipts matched glob: {DEFAULT_INPUT_GLOB}")
    return inputs, warnings, errors


def main() -> int:
    args = _parse_args()
    input_paths, warnings, errors = _load_inputs(args)
    selected_examples: list[dict[str, Any]] = []
    inspected_rows = 0
    tail_grid_item_count = 0
    input_row_count = 0

    for input_path in input_paths:
        payload, load_warnings, load_errors = _load_json(input_path)
        warnings.extend(load_warnings)
        errors.extend(load_errors)
        if payload is None:
            continue
        rows = _payload_rows(payload)
        input_row_count += len(rows)
        for row_index, row in enumerate(rows):
            inspected_rows += 1
            profile = row.get("best_profile") if isinstance(row.get("best_profile"), dict) else row.get("best_profile")
            if not isinstance(profile, dict):
                profile = None
            tail_items = _tail_grid_rows(profile)
            if tail_items:
                tail_grid_item_count += len(tail_items)
                for tail_item_index, tail_item in enumerate(tail_items):
                    example = _selected_example(
                        source_json=input_path,
                        row_index=row_index,
                        row=row,
                        profile=profile,
                        tail_item=tail_item,
                        tail_item_index=tail_item_index,
                        finite_shell_cutoff=int(args.finite_shell_cutoff),
                        low_tail_mass_threshold=float(args.low_tail_mass_threshold),
                    )
                    if example is not None:
                        selected_examples.append(example)
            else:
                example = _selected_example(
                    source_json=input_path,
                    row_index=row_index,
                    row=row,
                    profile=profile,
                    tail_item=None,
                    tail_item_index=None,
                    finite_shell_cutoff=int(args.finite_shell_cutoff),
                    low_tail_mass_threshold=float(args.low_tail_mass_threshold),
                )
                if example is not None:
                    selected_examples.append(example)

    selected_examples.sort(
        key=lambda item: (
            0 if item["selection_kind"] == "exact_finite_low_shell_degeneracy" else 1,
            float(item["q_gap_proxy"]) if item["q_gap_proxy"] is not None else float("inf"),
            float(item["priority_score"]) if item["priority_score"] is not None else float("-inf"),
            int(item["shell"]) if item["shell"] is not None else 10**9,
            int(item["snapshot_index"]) if item["snapshot_index"] is not None else 10**9,
            int(item["row_index"]),
        )
    )
    if args.max_selected >= 0:
        selected_examples = selected_examples[: int(args.max_selected)]

    exact_branch_count = sum(1 for item in selected_examples if item["selection_kind"] == "exact_finite_low_shell_degeneracy")
    proxy_branch_count = sum(1 for item in selected_examples if item["selection_kind"] == "proxy_finite_low_shell_degeneracy")
    exact_blocks_available_count = sum(1 for item in selected_examples if item["exact_blocks_available"])

    q_diag_values = [float(item["q_diag_proxy"]) for item in selected_examples if item["q_diag_proxy"] is not None]
    q_coup_values = [float(item["q_coup_proxy"]) for item in selected_examples if item["q_coup_proxy"] is not None]
    q_gap_values = [float(item["q_gap_proxy"]) for item in selected_examples if item["q_gap_proxy"] is not None]
    tail_mass_values = [float(item["tail_mass_proxy"]) for item in selected_examples if item["tail_mass_proxy"] is not None]
    shell_values = [int(item["shell"]) for item in selected_examples if item["shell"] is not None]

    aggregate = {
        "status": "partial",
        "candidate_only": True,
        "empirical_non_promoting": True,
        "fail_closed": True,
        "gpu_kn_authority": False,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "clay_promoted": False,
        "input_count": len(input_paths),
        "inspected_row_count": int(inspected_rows),
        "input_row_count": int(input_row_count),
        "selected_example_count": int(len(selected_examples)),
        "exact_example_count": int(exact_branch_count),
        "proxy_example_count": int(proxy_branch_count),
        "exact_blocks_available_count": int(exact_blocks_available_count),
        "tail_grid_item_count": int(tail_grid_item_count),
        "finite_shell_cutoff": int(args.finite_shell_cutoff),
        "low_tail_mass_threshold": float(args.low_tail_mass_threshold),
        "selected_shells": sorted(set(shell_values)),
        "q_diag_proxy_mean": _mean_or_none(q_diag_values),
        "q_diag_proxy_min": min(q_diag_values) if q_diag_values else None,
        "q_diag_proxy_max": max(q_diag_values) if q_diag_values else None,
        "q_coup_proxy_mean": _mean_or_none(q_coup_values),
        "q_coup_proxy_min": min(q_coup_values) if q_coup_values else None,
        "q_coup_proxy_max": max(q_coup_values) if q_coup_values else None,
        "q_gap_proxy_mean": _mean_or_none(q_gap_values),
        "q_gap_proxy_min": min(q_gap_values) if q_gap_values else None,
        "q_gap_proxy_max": max(q_gap_values) if q_gap_values else None,
        "tail_mass_proxy_mean": _mean_or_none(tail_mass_values),
        "tail_mass_proxy_max": max(tail_mass_values) if tail_mass_values else None,
        "tail_mass_proxy_min": min(tail_mass_values) if tail_mass_values else None,
        "priority_score_max": max(
            (float(item["priority_score"]) for item in selected_examples if item["priority_score"] is not None),
            default=None,
        ),
        "priority_score_min": min(
            (float(item["priority_score"]) for item in selected_examples if item["priority_score"] is not None),
            default=None,
        ),
        "selection_status": "exact" if exact_branch_count and not proxy_branch_count else "partial",
        "selection_note": "exact rows are rare; proxy rows are retained to prioritize exact Schur follow-up",
    }

    out = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "control_card": CONTROL_CARD,
        "status": "ok" if not errors else "error",
        "candidate_only": True,
        "empirical_non_promoting": True,
        "fail_closed": True,
        "gpu_kn_authority": False,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "clay_promoted": False,
        "input_jsons": [str(path) for path in input_paths],
        "rows": selected_examples,
        "aggregate": aggregate,
        "warnings": warnings,
        "errors": errors,
        "changed_files": [SCRIPT_NAME],
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    rendered = _json_text(out, pretty=args.pretty)
    args.output_json.write_text(rendered, encoding="utf-8")
    print(rendered)
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
