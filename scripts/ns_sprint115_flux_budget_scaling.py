#!/usr/bin/env python3
"""Sprint 115 thin-core reconnection flux-budget scaling calculator."""

from __future__ import annotations

import argparse
import csv
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint115_flux_budget_scaling"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint115_flux_budget_scaling")
SUMMARY_NAME = "ns_sprint115_flux_budget_scaling_summary.json"
ROWS_NAME = "ns_sprint115_flux_budget_scaling_rows.json"
CSV_NAME = "ns_sprint115_flux_budget_scaling_rows.csv"
REPORT_NAME = "ns_sprint115_flux_budget_scaling.md"

DELTA_OVER_B_VALUES = (0.10, 0.20, 0.30, 0.40, 0.48)
REYNOLDS_CORE_VALUES = (1.0e3, 1.0e4, 1.0e5)
CROW_GROWTH_TIME_FACTOR = 7.9
RECONNECT_TIME_FACTOR = 1.0
ANALYTIC_THRESHOLD_PROVED = False


@dataclass(frozen=True)
class FluxBudgetRow:
    delta_over_b: float
    reynolds_core: float
    elliptic_factor: float
    crow_growth_time_factor: float
    reconnect_time_factor: float
    viscous_condition_required: float
    re_delta: float
    viscous_window_ok: bool
    accumulation_fraction: float
    net_positive_factor: float
    certified_surplus_margin: float
    analytic_threshold_proved: bool
    complete: bool
    route_decision: str

    def as_row(self) -> dict[str, Any]:
        return asdict(self)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def compute_row(delta_over_b: float, reynolds_core: float) -> FluxBudgetRow:
    b_over_delta = 1.0 / delta_over_b
    elliptic_factor = delta_over_b**4
    viscous_condition_required = b_over_delta**2
    re_delta = reynolds_core * delta_over_b
    viscous_window_ok = re_delta > viscous_condition_required
    accumulation_fraction = RECONNECT_TIME_FACTOR / CROW_GROWTH_TIME_FACTOR
    net_positive_factor = max(0.0, 1.0 - elliptic_factor)
    certified_surplus_margin = (
        accumulation_fraction * net_positive_factor if viscous_window_ok else 0.0
    )
    complete = bool(ANALYTIC_THRESHOLD_PROVED)
    route_decision = "fail_unproved_k" + "star_collapse_threshold"

    return FluxBudgetRow(
        delta_over_b=delta_over_b,
        reynolds_core=reynolds_core,
        elliptic_factor=elliptic_factor,
        crow_growth_time_factor=CROW_GROWTH_TIME_FACTOR,
        reconnect_time_factor=RECONNECT_TIME_FACTOR,
        viscous_condition_required=viscous_condition_required,
        re_delta=re_delta,
        viscous_window_ok=viscous_window_ok,
        accumulation_fraction=accumulation_fraction,
        net_positive_factor=net_positive_factor,
        certified_surplus_margin=certified_surplus_margin,
        analytic_threshold_proved=ANALYTIC_THRESHOLD_PROVED,
        complete=complete,
        route_decision=route_decision,
    )


def build_rows() -> list[FluxBudgetRow]:
    return [
        compute_row(delta_over_b, reynolds_core)
        for delta_over_b in DELTA_OVER_B_VALUES
        for reynolds_core in REYNOLDS_CORE_VALUES
    ]


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        raise ValueError("cannot write empty row set")
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def format_float(value: float) -> str:
    return f"{value:.12g}"


def markdown_table(rows: list[dict[str, Any]]) -> str:
    headers = (
        "delta/b",
        "Re_core",
        "elliptic",
        "required",
        "Re_delta",
        "viscous ok",
        "surplus margin",
    )
    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    for row in rows:
        lines.append(
            "| "
            + " | ".join(
                (
                    format_float(row["delta_over_b"]),
                    format_float(row["reynolds_core"]),
                    format_float(row["elliptic_factor"]),
                    format_float(row["viscous_condition_required"]),
                    format_float(row["re_delta"]),
                    str(row["viscous_window_ok"]).lower(),
                    format_float(row["certified_surplus_margin"]),
                )
            )
            + " |"
        )
    return "\n".join(lines)


def write_report(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    text = "\n".join(
        (
            f"# {CONTRACT}",
            "",
            "Deterministic thin-core reconnection flux-budget scaling calculator.",
            "",
            "Formula surface:",
            "",
            "- elliptic_factor = (delta / b)^4",
            "- crow_growth_time_factor = 7.9",
            "- reconnect_time_factor = 1.0",
            "- viscous_condition_required = (b / delta)^2",
            "- viscous_window_ok = Re_delta > viscous_condition_required",
            "- accumulation_fraction = reconnect_time_factor / crow_growth_time_factor",
            "- net_positive_factor = max(0, 1 - elliptic_factor)",
            "- certified_surplus_margin = accumulation_fraction * net_positive_factor when viscous_window_ok else 0",
            "",
            "Closure status: incomplete. No analytic threshold proof flag is available.",
            f"Route decision: {summary['route_decision']}.",
            "",
            markdown_table(rows),
            "",
        )
    )
    path.write_text(text, encoding="utf-8")


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    positive_rows = [row for row in rows if row["certified_surplus_margin"] > 0.0]
    best_row = max(rows, key=lambda row: row["certified_surplus_margin"])
    route_decision = "fail_unproved_k" + "star_collapse_threshold"
    return {
        "contract": CONTRACT,
        "row_count": len(rows),
        "delta_over_b_values": list(DELTA_OVER_B_VALUES),
        "reynolds_core_values": list(REYNOLDS_CORE_VALUES),
        "crow_growth_time_factor": CROW_GROWTH_TIME_FACTOR,
        "reconnect_time_factor": RECONNECT_TIME_FACTOR,
        "analytic_threshold_proved": ANALYTIC_THRESHOLD_PROVED,
        "complete": bool(ANALYTIC_THRESHOLD_PROVED),
        "clay": False,
        "clay_promoted": False,
        "clay_navier_stokes_promoted": False,
        "viscous_window_ok_count": sum(1 for row in rows if row["viscous_window_ok"]),
        "positive_surplus_row_count": len(positive_rows),
        "max_certified_surplus_margin": best_row["certified_surplus_margin"],
        "max_margin_delta_over_b": best_row["delta_over_b"],
        "max_margin_reynolds_core": best_row["reynolds_core"],
        "route_decision": route_decision,
        "exit_code": 1,
        "exit_reason": "k-star collapse threshold is not proved",
    }


def main() -> int:
    args = parse_args()
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = args.repo_root / out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    rows = [row.as_row() for row in build_rows()]
    summary = build_summary(rows)

    write_json(out_dir / ROWS_NAME, rows)
    write_json(out_dir / SUMMARY_NAME, summary)
    write_csv(out_dir / CSV_NAME, rows)
    write_report(out_dir / REPORT_NAME, summary, rows)

    return 1


if __name__ == "__main__":
    sys.exit(main())
