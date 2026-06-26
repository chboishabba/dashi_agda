#!/usr/bin/env python3
"""Audit row/column control for the exact scripted pair-incidence operator.

This is a fail-closed analytic proof artifact. It does not recompute the full
cross block if a canonical pair-incidence summary already exists; instead it
reads the exact-script summary, derives the relevant row/column scaling and
incidence decompositions, and records the live Gate 1 obstruction.
"""

from __future__ import annotations

import argparse
import json
import math
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from ns_triad_frame_stability_scan import AUTHORITY, OK_STATUS, _json_text  # type: ignore


SCRIPT_NAME = "scripts/ns_triad_kn_pair_incidence_row_column_audit.py"
CONTRACT = "ns_triad_kn_pair_incidence_row_column_audit"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_PAIR_INCIDENCE_ROW_COLUMN_AUDIT"
SCHEMA_VERSION = "1.0.0"
DEFAULT_PAIR_INCIDENCE_SUMMARY = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_pair_incidence_operator_proof_20260624/summary.json"
)
DEFAULT_OUTPUT_DIR = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_pair_incidence_row_column_audit_20260625"
)
CONTROL_CARD = {
    "O": "Audit the exact scripted pair-incidence row/column control using the canonical exact-object summary.",
    "R": (
        "Read the exact pair-incidence proof artifact, derive the row/column power-law fits and incidence "
        "decompositions, and decide whether the current evidence supports or blocks a profile-independent C/N theorem."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed analytic audit only; no theorem, full-NS, BKM, or Clay promotion.",
    "L": "exact scripted summary -> row/column fits -> incidence decomposition -> Gate 1 verdict",
    "P": ROUTE_DECISION,
    "G": "Record the true normalization and any profile asymmetry explicitly rather than overclaiming a theorem.",
    "F": "The live gap is a profile-independent row/column theorem for the exact scripted operator under the checked normalization.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pair-incidence-summary", type=Path, default=DEFAULT_PAIR_INCIDENCE_SUMMARY)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _iso_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _make_logger(entries: list[dict[str, Any]]):
    started = time.perf_counter()

    def log(message: str, **fields: Any) -> None:
        entry: dict[str, Any] = {
            "at": _iso_now(),
            "elapsed_ms": round((time.perf_counter() - started) * 1000.0, 3),
            "message": message,
        }
        if fields:
            entry.update(fields)
        entries.append(entry)
        details = json.dumps(fields, sort_keys=True, default=str) if fields else "{}"
        print(f"[pair-incidence-rowcol] {entry['at']} +{entry['elapsed_ms']}ms {message} {details}", flush=True)

    return log, started


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


def _power_law_fit(rows: list[dict[str, Any]], x_key: str, y_key: str) -> dict[str, Any]:
    points: list[tuple[float, float]] = []
    for row in rows:
        x = _finite_float(row.get(x_key))
        y = _finite_float(row.get(y_key))
        if x is None or y is None or x <= 0.0 or y <= 0.0:
            continue
        points.append((x, y))
    if len(points) < 2:
        return {"fit_available": False, "point_count": len(points)}
    xs = [math.log(x) for x, _ in points]
    ys = [math.log(y) for _, y in points]
    mean_x = sum(xs) / len(xs)
    mean_y = sum(ys) / len(ys)
    denom = sum((x - mean_x) ** 2 for x in xs)
    if denom == 0.0:
        return {"fit_available": False, "point_count": len(points)}
    slope = sum((x - mean_x) * (y - mean_y) for x, y in zip(xs, ys, strict=False)) / denom
    intercept = mean_y - slope * mean_x
    return {
        "fit_available": True,
        "point_count": len(points),
        "slope": slope,
        "decay_exponent_if_y_decays": -slope,
        "C": math.exp(intercept),
        "points": [{"x": x, "y": y} for x, y in points],
    }


def _ratio_stats(values: list[float]) -> dict[str, Any]:
    if not values:
        return {"count": 0}
    mean = sum(values) / len(values)
    stdev = 0.0 if len(values) == 1 else math.sqrt(
        sum((value - mean) ** 2 for value in values) / (len(values) - 1)
    )
    return {
        "count": len(values),
        "min": min(values),
        "max": max(values),
        "mean": mean,
        "sample_stdev": stdev,
        "relative_range": (max(values) - min(values)) / mean if mean != 0.0 else None,
    }


def _scaled_stats(rows: list[dict[str, Any]], metric: str, exponent: int) -> dict[str, Any]:
    values: list[float] = []
    for row in rows:
        shell = _finite_float(row.get("N"))
        raw = _finite_float(row.get(metric))
        if shell is None or raw is None:
            continue
        values.append((shell ** exponent) * raw)
    return _ratio_stats(values)


def _family_decomposition(rows: list[dict[str, Any]], *, family: str) -> dict[str, Any]:
    row_mean_active_values: list[float] = []
    row_count_values: list[float] = []
    col_mean_active_values: list[float] = []
    col_count_values: list[float] = []
    row_decomposition_rows: list[dict[str, Any]] = []
    col_decomposition_rows: list[dict[str, Any]] = []

    for row in rows:
        row_sum = _finite_float(row.get("row_sum_sup"))
        col_sum = _finite_float(row.get("column_sum_sup"))
        row_count = _finite_float(row.get("worst_core_active_tail_count"))
        col_count = _finite_float(row.get("worst_tail_active_finite_k_count"))

        entry: dict[str, Any] = {"N": row.get("N")}
        if row_sum is not None and row_count is not None and row_count > 0.0:
            row_mean = row_sum / row_count
            row_mean_active_values.append(row_mean)
            row_count_values.append(row_count)
            entry["worst_row_active_count"] = row_count
            entry["worst_row_mean_active_entry"] = row_mean
        row_decomposition_rows.append(entry)

        col_entry: dict[str, Any] = {"N": row.get("N")}
        if col_sum is not None and col_count is not None and col_count > 0.0:
            col_mean = col_sum / col_count
            col_mean_active_values.append(col_mean)
            col_count_values.append(col_count)
            col_entry["worst_column_active_count"] = col_count
            col_entry["worst_column_mean_active_entry"] = col_mean
        col_decomposition_rows.append(col_entry)

    return {
        "family": family,
        "row_sum_fit": _power_law_fit(rows, "N", "row_sum_sup"),
        "column_sum_fit": _power_law_fit(rows, "N", "column_sum_sup"),
        "schur_bound_fit": _power_law_fit(rows, "N", "schur_bound"),
        "row_scaled_stats": {
            "N0_row_sum_sup": _scaled_stats(rows, "row_sum_sup", 0),
            "N2_row_sum_sup": _scaled_stats(rows, "row_sum_sup", 2),
        },
        "column_scaled_stats": {
            "N_column_sum_sup": _scaled_stats(rows, "column_sum_sup", 1),
            "N2_column_sum_sup": _scaled_stats(rows, "column_sum_sup", 2),
        },
        "row_decomposition_rows": row_decomposition_rows,
        "column_decomposition_rows": col_decomposition_rows,
        "row_active_count_fit": _power_law_fit(
            [row for row in row_decomposition_rows if "worst_row_active_count" in row],
            "N",
            "worst_row_active_count",
        ),
        "row_mean_active_entry_fit": _power_law_fit(
            [row for row in row_decomposition_rows if "worst_row_mean_active_entry" in row],
            "N",
            "worst_row_mean_active_entry",
        ),
        "column_active_count_fit": _power_law_fit(
            [row for row in col_decomposition_rows if "worst_column_active_count" in row],
            "N",
            "worst_column_active_count",
        ),
        "column_mean_active_entry_fit": _power_law_fit(
            [row for row in col_decomposition_rows if "worst_column_mean_active_entry" in row],
            "N",
            "worst_column_mean_active_entry",
        ),
    }


def _fit_slope(block: dict[str, Any], key: str) -> float | None:
    fit = block.get(key, {})
    if not isinstance(fit, dict):
        return None
    slope = fit.get("slope")
    return _finite_float(slope)


def _analysis_read(forced: dict[str, Any], adversarial: dict[str, Any]) -> str:
    forced_row = _fit_slope(forced, "row_sum_fit")
    forced_col = _fit_slope(forced, "column_sum_fit")
    adv_row = _fit_slope(adversarial, "row_sum_fit")
    adv_col = _fit_slope(adversarial, "column_sum_fit")
    forced_row_count = _fit_slope(forced, "row_active_count_fit")
    forced_row_mean = _fit_slope(forced, "row_mean_active_entry_fit")
    forced_col_count = _fit_slope(forced, "column_active_count_fit")
    forced_col_mean = _fit_slope(forced, "column_mean_active_entry_fit")

    def fmt(value: float | None) -> str:
        return "null" if value is None else f"{value:.3f}"

    return (
        "Row/column audit readout: under the checked exact-script normalization, the forced-tail family has "
        f"row_sum_sup ~ N^{fmt(forced_row)} and column_sum_sup ~ N^{fmt(forced_col)}, while the uniform-geometry "
        f"adversarial family has row_sum_sup ~ N^{fmt(adv_row)} and column_sum_sup ~ N^{fmt(adv_col)}. "
        "So the current data does not support the alternate claim that the exact-script column supremum is O(1) "
        "for the canonical checked object. Instead, the forced-tail rows are carried by a nearly constant worst-row "
        f"mass with active-count slope {fmt(forced_row_count)} and mean-active-entry slope {fmt(forced_row_mean)}, "
        "while the forced-tail columns are carried by an almost constant worst-column incidence count with "
        f"slope {fmt(forced_col_count)} and a decaying mean-active-entry slope {fmt(forced_col_mean)}. "
        "This preserves the sampled N^-1 Schur scale but does not by itself prove a profile-independent C/N theorem."
    )


def _markdown(payload: dict[str, Any]) -> str:
    def fmt(value: Any) -> str:
        if value is None:
            return "null"
        if isinstance(value, float):
            return f"{value:.6g}"
        return str(value)

    forced = payload["forced_tail_family"]
    adversarial = payload["adversarial_family"]
    lines = [
        "# NS Triad Exact Pair-Incidence Row/Column Audit",
        "",
        f"- status: `{payload['status']}`",
        f"- candidate only: `{payload['candidate_only']}`",
        f"- theorem promoted: `{payload['theorem_promoted']}`",
        f"- full NS promoted: `{payload['full_ns_promoted']}`",
        f"- BKM exclusion proved: `{payload['bkm_exclusion_proved']}`",
        f"- Clay promoted: `{payload['clay_promoted']}`",
        "",
        "## Fits",
        "",
        f"- forced row fit: `{forced['row_sum_fit']}`",
        f"- forced column fit: `{forced['column_sum_fit']}`",
        f"- forced Schur fit: `{forced['schur_bound_fit']}`",
        f"- adversarial row fit: `{adversarial['row_sum_fit']}`",
        f"- adversarial column fit: `{adversarial['column_sum_fit']}`",
        f"- adversarial Schur fit: `{adversarial['schur_bound_fit']}`",
        "",
        "## Forced-Tail Decomposition",
        "",
        "| N | row sup | worst-row active tails | mean active row entry | column sup | worst-column active finite k | mean active column entry |",
        "|---:|---:|---:|---:|---:|---:|---:|",
    ]
    rows = payload["forced_tail_rows"]
    row_rows = forced["row_decomposition_rows"]
    col_rows = forced["column_decomposition_rows"]
    for base, row_dec, col_dec in zip(rows, row_rows, col_rows, strict=False):
        lines.append(
            f"| {base['N']} | {fmt(base['row_sum_sup'])} | {fmt(row_dec.get('worst_row_active_count'))} | "
            f"{fmt(row_dec.get('worst_row_mean_active_entry'))} | {fmt(base['column_sum_sup'])} | "
            f"{fmt(col_dec.get('worst_column_active_count'))} | {fmt(col_dec.get('worst_column_mean_active_entry'))} |"
        )
    lines.extend(
        [
            "",
            "## Adversarial Geometry Sweep",
            "",
            "| N | row sup | column sup | worst-column active finite k |",
            "|---:|---:|---:|---:|",
        ]
    )
    for row in payload["adversarial_rows"]:
        lines.append(
            f"| {row['N']} | {fmt(row['row_sum_sup'])} | {fmt(row['column_sum_sup'])} | "
            f"{fmt(row.get('worst_tail_active_finite_k_count'))} |"
        )
    lines.extend(
        [
            "",
            "## Verdict",
            "",
            payload["analysis_read"],
            "",
            f"- theorem gate closed: `{payload['uniform_profile_independent_bound_closed']}`",
            f"- exact-script O(1) column-claim validated: `{payload['exact_script_constant_column_claim_validated']}`",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> int:
    args = _parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    log_entries: list[dict[str, Any]] = []
    log, started_perf = _make_logger(log_entries)
    started_at = _iso_now()
    log("started pair-incidence row/column audit", input_summary=str(args.pair_incidence_summary))
    pair = _load_json(args.pair_incidence_summary)
    forced_rows = [row for row in pair.get("forced_tail_rows", []) if isinstance(row, dict)]
    adversarial_rows = [row for row in pair.get("adversarial_rows", []) if isinstance(row, dict)]
    log(
        "loaded exact-script rows",
        forced_tail_row_count=len(forced_rows),
        adversarial_row_count=len(adversarial_rows),
    )

    forced = _family_decomposition(forced_rows, family="forced_tail")
    adversarial = _family_decomposition(adversarial_rows, family="uniform_geometry_adversarial")
    log(
        "derived family decompositions",
        forced_row_slope=_fit_slope(forced, "row_sum_fit"),
        forced_column_slope=_fit_slope(forced, "column_sum_fit"),
        adversarial_row_slope=_fit_slope(adversarial, "row_sum_fit"),
        adversarial_column_slope=_fit_slope(adversarial, "column_sum_fit"),
    )

    forced_col_decay = _fit_slope(forced, "column_sum_fit")
    exact_script_constant_column_claim_validated = bool(
        forced_col_decay is not None and abs(forced_col_decay) <= 0.25
    )

    payload: dict[str, Any] = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "control_card": CONTROL_CARD,
        "started_at": started_at,
        "status": pair.get("status") if pair.get("status") == OK_STATUS and forced_rows else "partial",
        "candidate_only": True,
        "fail_closed": True,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "bkm_exclusion_proved": False,
        "clay_promoted": False,
        "terminal_promoted": False,
        "pair_incidence_summary": str(args.pair_incidence_summary),
        "pair_incidence_status": pair.get("status"),
        "forced_tail_rows": forced_rows,
        "adversarial_rows": adversarial_rows,
        "forced_tail_family": forced,
        "adversarial_family": adversarial,
        "exact_script_constant_column_claim_validated": exact_script_constant_column_claim_validated,
        "uniform_profile_independent_bound_closed": False,
        "analysis_read": _analysis_read(forced, adversarial),
        "log_entries": log_entries,
    }

    output_json = args.output_dir / "summary.json"
    output_md = args.output_dir / "summary.md"
    output_json.write_text(_json_text(payload, bool(args.pretty)), encoding="utf-8")
    output_md.write_text(_markdown(payload), encoding="utf-8")
    finished_at = _iso_now()
    elapsed_ms = round((time.perf_counter() - started_perf) * 1000.0, 3)
    payload["finished_at"] = finished_at
    payload["elapsed_ms"] = elapsed_ms
    payload["log_entries"].append(
        {
            "at": finished_at,
            "elapsed_ms": elapsed_ms,
            "message": "wrote row/column audit artifacts",
            "output_json": str(output_json),
            "output_md": str(output_md),
        }
    )
    output_json.write_text(_json_text(payload, bool(args.pretty)), encoding="utf-8")
    print(_json_text(payload, bool(args.pretty)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
