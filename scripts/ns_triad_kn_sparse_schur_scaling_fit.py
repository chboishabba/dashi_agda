#!/usr/bin/env python3
"""Merge sparse-Schur scaling receipts and fit candidate decay laws.

This is a candidate-only reporting layer.  It reads summary receipts produced by
``ns_triad_kn_sparse_schur_scaling.py`` and emits derived telemetry such as
``N^2 q_gap``, ``D q_gap``, and log-log fits.  It does not run eigensolves and
does not promote a theorem.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

from ns_triad_frame_stability_scan import AUTHORITY, OK_STATUS, _json_text  # type: ignore


SCRIPT_NAME = "scripts/ns_triad_kn_sparse_schur_scaling_fit.py"
CONTRACT = "ns_triad_kn_sparse_schur_scaling_fit"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_SPARSE_SCHUR_SCALING_FIT"
SCHEMA_VERSION = "1.0.0"
DEFAULT_OUTPUT_DIR = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_sparse_schur_scaling_fit_20260624"
)
DEFAULT_INPUTS = [
    Path(
        "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
        "ns_triad_kn_sparse_schur_scaling_20260624/summary.json"
    ),
    Path(
        "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
        "ns_triad_kn_sparse_schur_scaling_shell12_20260624/summary.json"
    ),
]


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-summary", action="append", type=Path, default=None)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: JSON root must be an object")
    return payload


def _finite_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _finite_int(value: Any) -> int | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = int(value)
    except (TypeError, ValueError):
        return None
    return parsed


def _log_log_fit(rows: list[dict[str, Any]], x_key: str, y_key: str) -> dict[str, Any]:
    points: list[tuple[float, float]] = []
    for row in rows:
        x = _finite_float(row.get(x_key))
        y = _finite_float(row.get(y_key))
        if x is not None and y is not None and x > 0.0 and y > 0.0:
            points.append((x, y))
    if len(points) < 2:
        return {"point_count": len(points), "fit_available": False}
    xs = [math.log(x) for x, _ in points]
    ys = [math.log(y) for _, y in points]
    mean_x = sum(xs) / len(xs)
    mean_y = sum(ys) / len(ys)
    var_x = sum((x - mean_x) ** 2 for x in xs)
    if var_x == 0.0:
        return {"point_count": len(points), "fit_available": False}
    slope = sum((x - mean_x) * (y - mean_y) for x, y in zip(xs, ys)) / var_x
    intercept = mean_y - slope * mean_x
    predictions = [intercept + slope * x for x in xs]
    ss_res = sum((y - pred) ** 2 for y, pred in zip(ys, predictions))
    ss_tot = sum((y - mean_y) ** 2 for y in ys)
    r_squared = None if ss_tot == 0.0 else 1.0 - ss_res / ss_tot
    return {
        "point_count": len(points),
        "fit_available": True,
        "x_key": x_key,
        "y_key": y_key,
        "power_law_form": f"{y_key} ~= C * {x_key}^slope",
        "slope": slope,
        "decay_exponent_if_y_decays": -slope,
        "C": math.exp(intercept),
        "log_intercept": intercept,
        "r_squared_log_space": r_squared,
        "points": [{"x": x, "y": y} for x, y in points],
    }


def _ratio_stats(values: list[float]) -> dict[str, Any]:
    if not values:
        return {"count": 0}
    mean = sum(values) / len(values)
    if len(values) == 1:
        stdev = 0.0
    else:
        stdev = math.sqrt(sum((value - mean) ** 2 for value in values) / (len(values) - 1))
    return {
        "count": len(values),
        "min": min(values),
        "max": max(values),
        "mean": mean,
        "sample_stdev": stdev,
        "relative_range": (max(values) - min(values)) / mean if mean != 0.0 else None,
    }


def _merge_rows(input_paths: list[Path]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    by_shell: dict[int, dict[str, Any]] = {}
    inputs: list[dict[str, Any]] = []
    for path in input_paths:
        payload = _load_json(path)
        inputs.append(
            {
                "path": str(path),
                "status": payload.get("status"),
                "row_count": payload.get("row_count"),
                "failure_count": payload.get("failure_count"),
                "candidate_only": payload.get("candidate_only"),
            }
        )
        rows = payload.get("rows", [])
        if not isinstance(rows, list):
            continue
        for raw in rows:
            if not isinstance(raw, dict):
                continue
            shell = _finite_int(raw.get("shell"))
            if shell is None:
                continue
            by_shell[shell] = dict(raw)
    return [by_shell[shell] for shell in sorted(by_shell)], inputs


def _derive_row(row: dict[str, Any]) -> dict[str, Any]:
    shell = _finite_float(row.get("shell"))
    d_value = _finite_float(row.get("D"))
    q_gap = _finite_float(row.get("q_gap"))
    r_tail = _finite_float(row.get("R_tail"))
    bkm_tail = _finite_float(row.get("bkm_tail_projection_squared_fraction"))
    derived = dict(row)
    derived["N"] = int(shell) if shell is not None else None
    derived["N_squared"] = shell * shell if shell is not None else None
    derived["N2_q_gap"] = shell * shell * q_gap if shell is not None and q_gap is not None else None
    derived["D_q_gap"] = d_value * q_gap if d_value is not None and q_gap is not None else None
    derived["D_over_N2"] = d_value / (shell * shell) if d_value is not None and shell not in {None, 0.0} else None
    derived["q_gap_over_D_inv"] = d_value * q_gap if d_value is not None and q_gap is not None else None
    derived["tail_margin_over_c0"] = r_tail - 0.25 if r_tail is not None else None
    derived["BKM_tail_projection_times_D"] = (
        bkm_tail * d_value if bkm_tail is not None and d_value is not None else None
    )
    return derived


def _markdown(payload: dict[str, Any]) -> str:
    def fmt(value: Any) -> str:
        if value is None:
            return "null"
        if isinstance(value, float):
            return f"{value:.6g}"
        return str(value)

    q_fit = payload["fits"]["q_gap_vs_N"]
    d_fit = payload["fits"]["D_vs_N"]
    lines = [
        "# NS Triad K_N Sparse Schur Scaling Fit",
        "",
        f"- status: `{payload['status']}`",
        f"- rows: `{payload['row_count']}`",
        f"- candidate only: `{payload['candidate_only']}`",
        f"- theorem promoted: `{payload['theorem_promoted']}`",
        f"- Clay promoted: `{payload['clay_promoted']}`",
        "",
        "| N | K | D | q_gap | N² q_gap | D q_gap | D/N² | R_tail | BKM tail proj² | cross L_neg frac |",
        "|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['N']} | {row['K']} | {fmt(row['D'])} | {fmt(row['q_gap'])} | "
            f"{fmt(row['N2_q_gap'])} | {fmt(row['D_q_gap'])} | {fmt(row['D_over_N2'])} | "
            f"{fmt(row['R_tail'])} | {fmt(row['bkm_tail_projection_squared_fraction'])} | "
            f"{fmt(row['cross_l_neg_fraction'])} |"
        )
    lines.extend(
        [
            "",
            "## Fits",
            "",
            f"- q_gap vs N: exponent `{fmt(q_fit.get('decay_exponent_if_y_decays'))}`, "
            f"C `{fmt(q_fit.get('C'))}`, log-space R² `{fmt(q_fit.get('r_squared_log_space'))}`",
            f"- D vs N: slope `{fmt(d_fit.get('slope'))}`, "
            f"C `{fmt(d_fit.get('C'))}`, log-space R² `{fmt(d_fit.get('r_squared_log_space'))}`",
            f"- D*q_gap stats: `{payload['product_stats']['D_q_gap']}`",
            f"- N²*q_gap stats: `{payload['product_stats']['N2_q_gap']}`",
            "",
            "## Interpretation",
            "",
            payload["interpretation"],
            "",
        ]
    )
    return "\n".join(lines)


def main() -> int:
    args = _parse_args()
    input_paths = args.input_summary if args.input_summary else DEFAULT_INPUTS
    args.output_dir.mkdir(parents=True, exist_ok=True)
    raw_rows, inputs = _merge_rows(input_paths)
    rows = [_derive_row(row) for row in raw_rows]
    rows.sort(key=lambda row: int(row.get("N") or 0))

    q_gaps = [float(row["q_gap"]) for row in rows if row.get("q_gap") is not None]
    r_tails = [float(row["R_tail"]) for row in rows if row.get("R_tail") is not None]
    d_q_gap = [float(row["D_q_gap"]) for row in rows if row.get("D_q_gap") is not None]
    n2_q_gap = [float(row["N2_q_gap"]) for row in rows if row.get("N2_q_gap") is not None]
    status = OK_STATUS if rows and all(input_row.get("status") == OK_STATUS for input_row in inputs) else "partial"
    q_fit = _log_log_fit(rows, "N", "q_gap")
    d_fit = _log_log_fit(rows, "N", "D")
    q_d_fit = _log_log_fit(rows, "D", "q_gap")
    interpretation = (
        "Candidate-only fitted telemetry for top-tail sparse Schur repair. "
        f"The merged rows have min R_tail={min(r_tails) if r_tails else None}, "
        f"min q_gap={min(q_gaps) if q_gaps else None}, and mean D*q_gap="
        f"{(sum(d_q_gap) / len(d_q_gap)) if d_q_gap else None}. "
        "The log-log fit is evidence for a scaling target, not a theorem; "
        "all promotion flags remain false."
    )
    payload: dict[str, Any] = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "status": status,
        "candidate_only": True,
        "fail_closed": True,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "clay_promoted": False,
        "inputs": inputs,
        "row_count": len(rows),
        "rows": rows,
        "min_R_tail": min(r_tails) if r_tails else None,
        "min_q_gap": min(q_gaps) if q_gaps else None,
        "fits": {
            "q_gap_vs_N": q_fit,
            "D_vs_N": d_fit,
            "q_gap_vs_D": q_d_fit,
        },
        "product_stats": {
            "D_q_gap": _ratio_stats(d_q_gap),
            "N2_q_gap": _ratio_stats(n2_q_gap),
        },
        "interpretation": interpretation,
    }
    output_json = args.output_dir / "summary.json"
    output_md = args.output_dir / "summary.md"
    output_json.write_text(_json_text(payload, bool(args.pretty)), encoding="utf-8")
    output_md.write_text(_markdown(payload), encoding="utf-8")
    print(_json_text(payload, bool(args.pretty)))
    return 0 if status == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
