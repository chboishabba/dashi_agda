#!/usr/bin/env python3
"""Report the Schur-subtraction bound anatomy for the mixed-tail K_N lane.

This is a candidate-only derivation layer. It reads the Schur-gap anatomy
receipt and emits a compact report aimed at the next analytic bridge:
whether the small normalized gap looks like a structural Schur residue or
needs a genuine subtraction bound.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

from ns_triad_frame_stability_scan import AUTHORITY, OK_STATUS, _json_text  # type: ignore


SCRIPT_NAME = "scripts/ns_triad_kn_schur_subtraction_bound.py"
CONTRACT = "ns_triad_kn_schur_subtraction_bound"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_SCHUR_SUBTRACTION_BOUND"
SCHEMA_VERSION = "1.0.0"
DEFAULT_INPUT_SUMMARY = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_schur_gap_anatomy_20260624/summary.json"
)
DEFAULT_OUTPUT_DIR = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_schur_subtraction_bound_20260624"
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


def _derive_row(row: dict[str, Any]) -> dict[str, Any]:
    shell = _finite_float(row.get("N")) or _finite_float(row.get("shell"))
    d_value = _finite_float(row.get("D"))
    q_gap = _finite_float(row.get("q_gap"))
    derived = dict(row)
    derived["q_gap_over_q_diag"] = _ratio(row.get("q_gap"), row.get("q_diag"))
    derived["q_schur_subtraction_over_q_diag"] = _ratio(
        row.get("q_schur_subtraction"), row.get("q_diag")
    )
    derived["D_q_gap"] = d_value * q_gap if d_value is not None and q_gap is not None else None
    derived["N2_q_gap"] = shell * shell * q_gap if shell is not None and q_gap is not None else None
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

    q_diag = [row["q_diag"] for row in rows if _finite_float(row.get("q_diag")) is not None]
    q_schur = [row["q_schur"] for row in rows if _finite_float(row.get("q_schur")) is not None]
    q_gap = [row["q_gap"] for row in rows if _finite_float(row.get("q_gap")) is not None]
    q_sub = [
        row["q_schur_subtraction"]
        for row in rows
        if _finite_float(row.get("q_schur_subtraction")) is not None
    ]
    q_gap_over_diag = [row["q_gap_over_q_diag"] for row in rows if row.get("q_gap_over_q_diag") is not None]
    q_sub_over_diag = [
        row["q_schur_subtraction_over_q_diag"]
        for row in rows
        if row.get("q_schur_subtraction_over_q_diag") is not None
    ]
    d_q_gap = [row["D_q_gap"] for row in rows if row.get("D_q_gap") is not None]
    n2_q_gap = [row["N2_q_gap"] for row in rows if row.get("N2_q_gap") is not None]

    def fmt(value: float | None) -> str:
        return "null" if value is None else f"{value:.6g}"

    return (
        "Candidate-only Schur-subtraction bound readout: q_diag and q_schur remain on the "
        f"10^-2 scale ({fmt(min(q_diag) if q_diag else None)}..{fmt(max(q_diag) if q_diag else None)}, "
        f"{fmt(min(q_schur) if q_schur else None)}..{fmt(max(q_schur) if q_schur else None)}), "
        f"q_sub/q_diag stays around {fmt(min(q_sub_over_diag) if q_sub_over_diag else None)}.."
        f"{fmt(max(q_sub_over_diag) if q_sub_over_diag else None)} rather than approaching 1, "
        f"q_gap remains positive and small ({fmt(min(q_gap) if q_gap else None)}..{fmt(max(q_gap) if q_gap else None)}), "
        f"q_gap/q_diag stays around {fmt(min(q_gap_over_diag) if q_gap_over_diag else None)}.."
        f"{fmt(max(q_gap_over_diag) if q_gap_over_diag else None)}, "
        f"D*q_gap averages about {fmt(sum(d_q_gap) / len(d_q_gap) if d_q_gap else None)}, "
        f"and N^2*q_gap averages about {fmt(sum(n2_q_gap) / len(n2_q_gap) if n2_q_gap else None)}."
    )


def _markdown(payload: dict[str, Any]) -> str:
    def fmt(value: Any) -> str:
        if value is None:
            return "null"
        if isinstance(value, float):
            return f"{value:.6g}"
        return str(value)

    def shell_or_n(row: dict[str, Any]) -> Any:
        return row.get("N", row.get("shell"))

    lines = [
        "# NS Triad K_N Schur Subtraction Bound",
        "",
        f"- status: `{payload['status']}`",
        f"- candidate only: `{payload['candidate_only']}`",
        f"- theorem promoted: `{payload['theorem_promoted']}`",
        f"- full NS promoted: `{payload['full_ns_promoted']}`",
        f"- BKM exclusion proved: `{payload['bkm_exclusion_proved']}`",
        f"- Clay promoted: `{payload['clay_promoted']}`",
        "",
        "| N | K | q_diag | q_schur | q_schur_subtraction | q_gap | q_gap/q_diag | q_schur_subtraction/q_diag | D | D*q_gap | N²*q_gap | R_tail | cross L_neg frac | BKM tail proj² |",
        "|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {shell_or_n(row)} | {row['K']} | {fmt(row['q_diag'])} | {fmt(row['q_schur'])} | "
            f"{fmt(row['q_schur_subtraction'])} | {fmt(row['q_gap'])} | "
            f"{fmt(row['q_gap_over_q_diag'])} | {fmt(row['q_schur_subtraction_over_q_diag'])} | "
            f"{fmt(row['D'])} | {fmt(row['D_q_gap'])} | {fmt(row['N2_q_gap'])} | "
            f"{fmt(row['R_tail'])} | {fmt(row['cross_l_neg_fraction'])} | "
            f"{fmt(row['bkm_tail_projection_squared_fraction'])} |"
        )
    lines.extend(
        [
            "",
            "## Readout",
            "",
            payload["analysis_read"],
            "",
            "## Row stats",
            "",
            f"- q_gap/q_diag stats: `{payload['ratio_stats']['q_gap_over_q_diag']}`",
            f"- q_schur_subtraction/q_diag stats: `{payload['ratio_stats']['q_schur_subtraction_over_q_diag']}`",
            f"- D*q_gap stats: `{payload['product_stats']['D_q_gap']}`",
            f"- N²*q_gap stats: `{payload['product_stats']['N2_q_gap']}`",
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

    q_gap_over_diag = [float(row["q_gap_over_q_diag"]) for row in rows if row.get("q_gap_over_q_diag") is not None]
    q_sub_over_diag = [
        float(row["q_schur_subtraction_over_q_diag"])
        for row in rows
        if row.get("q_schur_subtraction_over_q_diag") is not None
    ]
    d_q_gap = [float(row["D_q_gap"]) for row in rows if row.get("D_q_gap") is not None]
    n2_q_gap = [float(row["N2_q_gap"]) for row in rows if row.get("N2_q_gap") is not None]

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
        "ratio_stats": {
            "q_gap_over_q_diag": _ratio_stats(q_gap_over_diag),
            "q_schur_subtraction_over_q_diag": _ratio_stats(q_sub_over_diag),
        },
        "product_stats": {
            "D_q_gap": _ratio_stats(d_q_gap),
            "N2_q_gap": _ratio_stats(n2_q_gap),
        },
        "analysis_read": _diagnostic_read(rows),
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
