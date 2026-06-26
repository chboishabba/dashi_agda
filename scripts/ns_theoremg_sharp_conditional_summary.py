#!/usr/bin/env python3
"""Summarize the sharp conditional TheoremG route from CSV-backed calc surfaces."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_theoremg_sharp_conditional_summary.py"
CONTRACT = "ns_theoremg_sharp_conditional_summary"
DEFAULT_CALC6 = Path("/home/c/Downloads/calc6_results.csv")
DEFAULT_CLAY_SUMMARY = Path("/home/c/Downloads/ns_clay_calc_summary.csv")
DEFAULT_Q2_BOUNDS = Path("/home/c/Downloads/theoremG_Q2_bounds.csv")
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_theoremg_sharp_conditional_summary_20260620.json"
)

CONTROL_CARD = {
    "O": "Owner 5 summarizes the sharp conditional TheoremG route from the supplied CSV calc surfaces.",
    "R": (
        "Ingest Calc 6 geometry, the NS Clay margin summary, and TheoremG Q2 bounds; "
        "report whether the sharp conditional hypotheses and exponent gap remain supported."
    ),
    "C": SCRIPT_NAME,
    "S": (
        "The summary is fail-closed on missing CSVs, missing columns, or failed positivity/"
        "threshold checks."
    ),
    "L": (
        "read csv -> normalize numerics -> merge frame/time rows -> compute minima and "
        "exponent comparison -> emit deterministic JSON"
    ),
    "P": "FAIL_CLOSED_THEOREMG_SHARP_CONDITIONAL_SUMMARY",
    "G": "This script summarizes DNS-checkable support only; it does not promote a theorem or Clay result.",
    "F": (
        "A valid summary requires positive H_area/H_B support, delta1 > 1, and a positive "
        "exponent gap 2 - 2/delta1."
    ),
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--calc6-csv", type=Path, default=DEFAULT_CALC6)
    parser.add_argument("--clay-summary-csv", type=Path, default=DEFAULT_CLAY_SUMMARY)
    parser.add_argument("--q2-bounds-csv", type=Path, default=DEFAULT_Q2_BOUNDS)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _read_csv(path: Path) -> list[dict[str, str]]:
    if not path.exists():
        raise FileNotFoundError(f"missing CSV input: {path}")
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def _require_fields(rows: list[dict[str, str]], fields: tuple[str, ...], label: str) -> None:
    if not rows:
        raise ValueError(f"{label} is empty")
    missing = [field for field in fields if field not in rows[0]]
    if missing:
        raise KeyError(f"{label} missing required columns: {missing}")


def _float(value: str) -> float:
    return float(value)


def _min_float(rows: list[dict[str, str]], field: str) -> float:
    return min(_float(row[field]) for row in rows)


def _max_float(rows: list[dict[str, str]], field: str) -> float:
    return max(_float(row[field]) for row in rows)


def _mean_float(rows: list[dict[str, str]], field: str) -> float:
    return sum(_float(row[field]) for row in rows) / len(rows)


def _merge_rows(
    calc6_rows: list[dict[str, str]],
    clay_rows: list[dict[str, str]],
    q2_rows: list[dict[str, str]],
) -> list[dict[str, Any]]:
    clay_by_frame = {row["frame"]: row for row in clay_rows}
    q2_by_t = {row["t"]: row for row in q2_rows}
    merged: list[dict[str, Any]] = []

    for calc6 in calc6_rows:
        frame = calc6["frame"]
        t = calc6["t"]
        clay = clay_by_frame.get(frame)
        q2 = q2_by_t.get(t)
        if clay is None:
            raise KeyError(f"missing clay summary row for frame {frame}")
        if q2 is None:
            raise KeyError(f"missing q2 bounds row for t={t}")
        merged.append(
            {
                "frame": int(frame),
                "t": _float(t),
                "H_area_direct": _float(calc6["area_direct"]),
                "H_area_isop_lower": _float(calc6["area_isop_lower"]),
                "H_B_rho_min": _float(calc6["rho_min"]),
                "H_g12_min": _float(calc6["min_g12"]),
                "betti0": int(calc6["betti0"]),
                "q2_coeff": _float(calc6["q2_coeff"]),
                "lambda3_proxy": _float(clay["lambda3_proxy"]),
                "F123_damp_coeff": _float(clay["F123_damp_coeff"]),
                "net_margin": _float(clay["net_margin"]),
                "delta1": _float(q2["delta1"]),
                "Q2_lower": _float(q2["Q2_lower"]),
                "Q2_upper": _float(q2["Q2_upper"]),
                "Q2_ratio": _float(q2["ratio"]),
                "exp_gap": _float(q2["exp_gap"]),
            }
        )

    return merged


def _build_payload(
    calc6_rows: list[dict[str, str]],
    clay_rows: list[dict[str, str]],
    q2_rows: list[dict[str, str]],
) -> dict[str, Any]:
    merged_rows = _merge_rows(calc6_rows, clay_rows, q2_rows)

    min_area_direct = _min_float(calc6_rows, "area_direct")
    min_area_isop = _min_float(calc6_rows, "area_isop_lower")
    min_rho = _min_float(calc6_rows, "rho_min")
    min_g12 = min(_float(row["H_g12_min"]) for row in merged_rows)
    min_delta1 = _min_float(q2_rows, "delta1")
    min_exp_gap = _min_float(q2_rows, "exp_gap")
    min_q2_ratio = _min_float(q2_rows, "ratio")
    max_q2_ratio = _max_float(q2_rows, "ratio")
    lower_exponent = 2.0
    upper_exponent = lower_exponent / min_delta1
    exponent_margin = lower_exponent - upper_exponent

    support_flags = {
        "H_area_direct_positive": min_area_direct > 0.0,
        "H_area_isop_positive": min_area_isop > 0.0,
        "H_B_positive": min_rho > 0.0,
        "H_g12_positive": min_g12 > 0.0,
        "H_g12_sharp_delta1_gt_1": min_delta1 > 1.0,
        "exponent_gap_positive": exponent_margin > 0.0,
        "reported_exp_gap_positive": min_exp_gap > 0.0,
    }

    return {
        "contract": CONTRACT,
        "control_card": CONTROL_CARD,
        "status": "ok" if all(support_flags.values()) else "error",
        "inputs": {
            "calc6_rows": len(calc6_rows),
            "clay_summary_rows": len(clay_rows),
            "q2_bounds_rows": len(q2_rows),
        },
        "hypothesis_support": {
            "H_area_direct_min": min_area_direct,
            "H_area_isop_lower_min": min_area_isop,
            "H_B_rho_min": min_rho,
            "H_g12_min": min_g12,
            "delta1_min": min_delta1,
            "support_flags": support_flags,
        },
        "exponent_comparison": {
            "lower_exponent": lower_exponent,
            "upper_exponent_max": upper_exponent,
            "exponent_margin": exponent_margin,
            "reported_exp_gap_min": min_exp_gap,
        },
        "telemetry": {
            "q2_ratio_min": min_q2_ratio,
            "q2_ratio_max": max_q2_ratio,
            "net_margin_min": _min_float(clay_rows, "net_margin"),
            "net_margin_mean": _mean_float(clay_rows, "net_margin"),
            "F123_damp_coeff_min": _min_float(clay_rows, "F123_damp_coeff"),
            "area_direct_mean": _mean_float(calc6_rows, "area_direct"),
            "betti0_min": min(int(row["betti0"]) for row in calc6_rows),
        },
        "merged_rows": merged_rows,
        "errors": [],
    }


def main() -> int:
    args = _parse_args()
    calc6_rows = _read_csv(args.calc6_csv)
    clay_rows = _read_csv(args.clay_summary_csv)
    q2_rows = _read_csv(args.q2_bounds_csv)

    _require_fields(
        calc6_rows,
        ("frame", "t", "area_direct", "area_isop_lower", "min_g12", "rho_min", "betti0", "q2_coeff"),
        "calc6",
    )
    _require_fields(
        clay_rows,
        ("frame", "t", "lambda3_proxy", "F123_damp_coeff", "net_margin"),
        "ns_clay_calc_summary",
    )
    _require_fields(
        q2_rows,
        ("t", "Q2_lower", "Q2_upper", "ratio", "delta1", "exp_gap"),
        "theoremG_Q2_bounds",
    )

    payload = _build_payload(calc6_rows, clay_rows, q2_rows)
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(
        json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if payload["status"] == "ok" else 1


if __name__ == "__main__":
    raise SystemExit(main())
