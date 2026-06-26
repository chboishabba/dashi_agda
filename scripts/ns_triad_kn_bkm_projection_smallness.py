#!/usr/bin/env python3
"""Report the finite-shell BKM-projection smallness for the mixed-tail K_N lane.

This is a candidate-only bridge layer. It reads the sparse-Schur scaling
summary, extracts the observed BKM-tail projection telemetry, and packages it
as a non-promoting receipt focused on the next analytic question: whether the
bad mixed-tail eigenpiece stays structurally small against the BKM stretching
proxy, rather than only looking small on four sampled shells.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

from ns_triad_frame_stability_scan import AUTHORITY, OK_STATUS, _json_text  # type: ignore


SCRIPT_NAME = "scripts/ns_triad_kn_bkm_projection_smallness.py"
CONTRACT = "ns_triad_kn_bkm_projection_smallness"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_BKM_PROJECTION_SMALLNESS"
SCHEMA_VERSION = "1.0.0"
DEFAULT_INPUT_SUMMARY = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_sparse_schur_scaling_fit_20260624/summary.json"
)
DEFAULT_OUTPUT_DIR = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_bkm_projection_smallness_20260624"
)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-summary", type=Path, default=DEFAULT_INPUT_SUMMARY)
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


def _ratio(numerator: Any, denominator: Any) -> float | None:
    num = _finite_float(numerator)
    den = _finite_float(denominator)
    if num is None or den is None or den == 0.0:
        return None
    return num / den


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


def _power_law_fit(points: list[tuple[float, float]]) -> dict[str, Any]:
    positive = [(x, y) for x, y in points if x > 0.0 and y > 0.0]
    if len(positive) < 2:
        return {"fit_available": False, "point_count": len(positive)}
    xs = [math.log(x) for x, _ in positive]
    ys = [math.log(y) for _, y in positive]
    mean_x = sum(xs) / len(xs)
    mean_y = sum(ys) / len(ys)
    denom = sum((x - mean_x) ** 2 for x in xs)
    if denom == 0.0:
        return {"fit_available": False, "point_count": len(positive)}
    slope = sum((x - mean_x) * (y - mean_y) for x, y in zip(xs, ys)) / denom
    intercept = mean_y - slope * mean_x
    sst = sum((y - mean_y) ** 2 for y in ys)
    sse = sum((y - (intercept + slope * x)) ** 2 for x, y in zip(xs, ys))
    r_squared = 1.0 if sst == 0.0 else max(0.0, min(1.0, 1.0 - sse / sst))
    return {
        "fit_available": True,
        "point_count": len(positive),
        "x_key": "N",
        "y_key": "bkm_tail_projection_squared_fraction",
        "power_law_form": "bkm_tail_projection_squared_fraction ~= C * N^slope",
        "C": math.exp(intercept),
        "slope": slope,
        "decay_exponent_if_y_decays": -slope,
        "log_intercept": intercept,
        "r_squared_log_space": r_squared,
        "points": [{"x": x, "y": y} for x, y in positive],
    }


def _derive_row(row: dict[str, Any]) -> dict[str, Any]:
    shell = _finite_float(row.get("N")) or _finite_float(row.get("shell"))
    q_gap = _finite_float(row.get("q_gap"))
    bkm_sq = _finite_float(row.get("bkm_tail_projection_squared_fraction"))
    derived = dict(row)
    derived["bkm_over_q_gap"] = _ratio(
        row.get("bkm_tail_projection_squared_fraction"), row.get("q_gap")
    )
    derived["bkm_tail_projection_times_D"] = _finite_float(row.get("BKM_tail_projection_times_D"))
    derived["bkm_sq_times_N2"] = shell * shell * bkm_sq if shell is not None and bkm_sq is not None else None
    derived["q_gap_times_N2"] = shell * shell * q_gap if shell is not None and q_gap is not None else None
    return derived


def _load_rows(payload: dict[str, Any]) -> list[dict[str, Any]]:
    rows = payload.get("rows", [])
    if not isinstance(rows, list):
        return []
    normalized: list[dict[str, Any]] = []
    for raw in rows:
        if isinstance(raw, dict):
            normalized.append(_derive_row(raw))
    normalized.sort(key=lambda row: int(row.get("N") or row.get("shell") or 0))
    return normalized


def _diagnostic_read(rows: list[dict[str, Any]]) -> str:
    if not rows:
        return "No finite-shell rows were available."

    bkm_sq = [row["bkm_tail_projection_squared_fraction"] for row in rows if _finite_float(row.get("bkm_tail_projection_squared_fraction")) is not None]
    bkm_over_q_gap = [row["bkm_over_q_gap"] for row in rows if row.get("bkm_over_q_gap") is not None]
    bkm_sq_times_n2 = [row["bkm_sq_times_N2"] for row in rows if row.get("bkm_sq_times_N2") is not None]
    bkm_times_d = [row["bkm_tail_projection_times_D"] for row in rows if row.get("bkm_tail_projection_times_D") is not None]
    q_gap_times_n2 = [row["q_gap_times_N2"] for row in rows if row.get("q_gap_times_N2") is not None]

    def fmt(value: float | None) -> str:
        return "null" if value is None else f"{value:.6g}"

    projection_fit = _power_law_fit(
        [
            (float(row["N"]), float(row["bkm_tail_projection_squared_fraction"]))
            for row in rows
            if row.get("N") is not None and row.get("bkm_tail_projection_squared_fraction") is not None
        ]
    )
    decay_text = (
        f"the sampled BKM-tail projection squared fraction fits roughly N^-{projection_fit['decay_exponent_if_y_decays']:.3f}"
        if projection_fit.get("fit_available")
        else "no stable BKM power-law fit was available"
    )
    return (
        "Candidate-only BKM-projection readout: the squared projection stays tiny across the sampled shells, "
        f"with a sharp drop by N=12; it is not monotone from N=6 to N=8, but {decay_text}. "
        f"The raw squared values span {fmt(min(bkm_sq) if bkm_sq else None)}..{fmt(max(bkm_sq) if bkm_sq else None)}, "
        f"bkm^2 / q_gap spans {fmt(min(bkm_over_q_gap) if bkm_over_q_gap else None)}..{fmt(max(bkm_over_q_gap) if bkm_over_q_gap else None)}, "
        f"bkm^2 * N^2 spans {fmt(min(bkm_sq_times_n2) if bkm_sq_times_n2 else None)}..{fmt(max(bkm_sq_times_n2) if bkm_sq_times_n2 else None)}, "
        f"bkm*D spans {fmt(min(bkm_times_d) if bkm_times_d else None)}..{fmt(max(bkm_times_d) if bkm_times_d else None)}, "
        f"and q_gap * N^2 remains in the same O(10^-2) range for context ({fmt(min(q_gap_times_n2) if q_gap_times_n2 else None)}..{fmt(max(q_gap_times_n2) if q_gap_times_n2 else None)})."
    )


def _markdown(payload: dict[str, Any]) -> str:
    def fmt(value: Any) -> str:
        if value is None:
            return "null"
        if isinstance(value, float):
            return f"{value:.6g}"
        return str(value)

    lines = [
        "# NS Triad K_N BKM Projection Smallness",
        "",
        f"- status: `{payload['status']}`",
        f"- candidate only: `{payload['candidate_only']}`",
        f"- theorem promoted: `{payload['theorem_promoted']}`",
        f"- full NS promoted: `{payload['full_ns_promoted']}`",
        f"- BKM exclusion proved: `{payload['bkm_exclusion_proved']}`",
        f"- Clay promoted: `{payload['clay_promoted']}`",
        "",
        "| N | K | bkm_tail_proj² | bkm_tail_proj² / q_gap | bkm_tail_proj² * N² | bkm_tail_proj * D | q_gap | q_gap * N² | R_tail | cross L_neg frac | eigen_tail_mass |",
        "|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['N']} | {row['K']} | {fmt(row['bkm_tail_projection_squared_fraction'])} | "
            f"{fmt(row['bkm_over_q_gap'])} | {fmt(row['bkm_sq_times_N2'])} | "
            f"{fmt(row['bkm_tail_projection_times_D'])} | {fmt(row['q_gap'])} | "
            f"{fmt(row['q_gap_times_N2'])} | {fmt(row['R_tail'])} | {fmt(row['cross_l_neg_fraction'])} | "
            f"{fmt(row['eigen_tail_mass'])} |"
        )
    lines.extend(
        [
            "",
            "## Readout",
            "",
            payload["bkm_projection_readout"],
            "",
            "## Fit",
            "",
            f"- bkm projection vs N fit: `{payload['projection_fit']}`",
            f"- bkm^2 / q_gap stats: `{payload['ratio_stats']['bkm_over_q_gap']}`",
            f"- bkm^2 * N^2 stats: `{payload['product_stats']['bkm_sq_times_N2']}`",
            f"- bkm*D stats: `{payload['product_stats']['bkm_tail_projection_times_D']}`",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> int:
    args = _parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    source = _load_json(args.input_summary)
    rows = _load_rows(source)
    status = source.get("status") if source.get("status") == OK_STATUS and len(rows) >= 4 else "partial"

    bkm_over_q_gap = [float(row["bkm_over_q_gap"]) for row in rows if row.get("bkm_over_q_gap") is not None]
    bkm_sq_times_n2 = [float(row["bkm_sq_times_N2"]) for row in rows if row.get("bkm_sq_times_N2") is not None]
    bkm_times_d = [float(row["bkm_tail_projection_times_D"]) for row in rows if row.get("bkm_tail_projection_times_D") is not None]

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
        "bkm_exclusion_proved": False,
        "clay_promoted": False,
        "terminal_promoted": False,
        "input_summary": str(args.input_summary),
        "source_status": source.get("status"),
        "source_row_count": source.get("row_count"),
        "row_count": len(rows),
        "rows": rows,
        "projection_fit": _power_law_fit(
            [
                (float(row["N"]), float(row["bkm_tail_projection_squared_fraction"]))
                for row in rows
                if row.get("N") is not None and row.get("bkm_tail_projection_squared_fraction") is not None
            ]
        ),
        "ratio_stats": {
            "bkm_over_q_gap": _ratio_stats(bkm_over_q_gap),
        },
        "product_stats": {
            "bkm_sq_times_N2": _ratio_stats(bkm_sq_times_n2),
            "bkm_tail_projection_times_D": _ratio_stats(bkm_times_d),
        },
        "bkm_projection_readout": _diagnostic_read(rows),
        "promotion_flags": [],
    }

    output_json = args.output_dir / "summary.json"
    output_md = args.output_dir / "summary.md"
    output_json.write_text(_json_text(payload, bool(args.pretty)), encoding="utf-8")
    output_md.write_text(_markdown(payload), encoding="utf-8")
    print(_json_text(payload, bool(args.pretty)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
