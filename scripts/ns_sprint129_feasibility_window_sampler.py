#!/usr/bin/env python3
"""Sprint 129 NS feasibility-window sampler.

This is a deterministic model-level sampler.  It scans alpha in [0.75, 1.75],
sets beta=alpha-1, and records which rows survive the formal feasibility
gates for BKM divergence, concentration, u1 viscosity, NSE consistency, and
membership in the recommended open window (1, 3/2).
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint129_feasibility_window_sampler"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint129_feasibility_window_sampler")
SUMMARY_NAME = "ns_sprint129_feasibility_window_sampler_summary.json"
ROWS_NAME = "ns_sprint129_feasibility_window_sampler_rows.json"
CSV_NAME = "ns_sprint129_feasibility_window_sampler_rows.csv"
REPORT_NAME = "ns_sprint129_feasibility_window_sampler.md"

ALPHA_START = Fraction(3, 4)
ALPHA_STOP = Fraction(7, 4)
ALPHA_STEP = Fraction(1, 20)
RECOMMENDED_ALPHA_WINDOW = (Fraction(1, 1), Fraction(3, 2))


@dataclass(frozen=True)
class FeasibilityWindowRow:
    row_id: str
    alpha: float
    alpha_fraction: str
    beta: float
    beta_fraction: str
    bkm_divergence_classification: str
    bkm_divergence_survives: bool
    concentration_classification: str
    concentration_survives: bool
    u1_viscosity_classification: str
    u1_viscosity_survives: bool
    nse_consistency_classification: str
    nse_consistent: bool
    in_recommended_alpha_window: bool
    viable: bool
    boundary_failure: bool
    classification: str

    def as_row(self) -> dict[str, Any]:
        return asdict(self)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def alpha_values() -> list[Fraction]:
    count = int((ALPHA_STOP - ALPHA_START) / ALPHA_STEP)
    return [ALPHA_START + index * ALPHA_STEP for index in range(count + 1)]


def fmt_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def bkm_classification(alpha: Fraction) -> tuple[str, bool]:
    if alpha >= RECOMMENDED_ALPHA_WINDOW[1]:
        return ("bkm_endpoint_or_supercritical_divergence_obstructed", False)
    if alpha <= RECOMMENDED_ALPHA_WINDOW[0]:
        return ("bkm_subcritical_side_not_decisive", True)
    return ("bkm_divergence_gate_survives", True)


def concentration_classification(alpha: Fraction) -> tuple[str, bool]:
    if alpha <= RECOMMENDED_ALPHA_WINDOW[0]:
        return ("concentration_too_weak_at_lower_side", False)
    if alpha >= RECOMMENDED_ALPHA_WINDOW[1]:
        return ("concentration_survives_but_bkm_obstructed", True)
    return ("concentration_gate_survives", True)


def u1_viscosity_classification(alpha: Fraction) -> tuple[str, bool]:
    lower, upper = RECOMMENDED_ALPHA_WINDOW
    if lower < alpha < upper:
        return ("u1_viscosity_survives_inside_open_window", True)
    if alpha <= lower:
        return ("u1_viscosity_lost_at_or_below_alpha_one", False)
    return ("u1_viscosity_lost_at_or_above_alpha_three_halves", False)


def nse_consistency_classification(alpha: Fraction, beta: Fraction) -> tuple[str, bool]:
    if beta != alpha - 1:
        return ("nse_scaling_relation_failed", False)
    if alpha <= 0:
        return ("nse_alpha_nonpositive", False)
    return ("nse_scaling_relation_consistent", True)


def classify(
    bkm_survives: bool,
    concentration_survives: bool,
    u1_survives: bool,
    nse_consistent: bool,
    in_window: bool,
) -> str:
    if all((bkm_survives, concentration_survives, u1_survives, nse_consistent, in_window)):
        return "viable_inside_open_feasibility_window"
    failed = []
    if not bkm_survives:
        failed.append("bkm")
    if not concentration_survives:
        failed.append("concentration")
    if not u1_survives:
        failed.append("u1_viscosity")
    if not nse_consistent:
        failed.append("nse_consistency")
    if not in_window:
        failed.append("recommended_window")
    return "boundary_or_gate_failure_" + "_".join(failed)


def build_rows() -> list[FeasibilityWindowRow]:
    rows: list[FeasibilityWindowRow] = []
    lower, upper = RECOMMENDED_ALPHA_WINDOW
    for alpha in alpha_values():
        beta = alpha - 1
        bkm_class, bkm_survives = bkm_classification(alpha)
        concentration_class, concentration_survives = concentration_classification(alpha)
        u1_class, u1_survives = u1_viscosity_classification(alpha)
        nse_class, nse_consistent = nse_consistency_classification(alpha, beta)
        in_window = lower < alpha < upper
        viable = (
            bkm_survives
            and concentration_survives
            and u1_survives
            and nse_consistent
            and in_window
        )
        rows.append(
            FeasibilityWindowRow(
                row_id=f"r{len(rows):03d}",
                alpha=float(alpha),
                alpha_fraction=fmt_fraction(alpha),
                beta=float(beta),
                beta_fraction=fmt_fraction(beta),
                bkm_divergence_classification=bkm_class,
                bkm_divergence_survives=bkm_survives,
                concentration_classification=concentration_class,
                concentration_survives=concentration_survives,
                u1_viscosity_classification=u1_class,
                u1_viscosity_survives=u1_survives,
                nse_consistency_classification=nse_class,
                nse_consistent=nse_consistent,
                in_recommended_alpha_window=in_window,
                viable=viable,
                boundary_failure=not viable,
                classification=classify(
                    bkm_survives,
                    concentration_survives,
                    u1_survives,
                    nse_consistent,
                    in_window,
                ),
            )
        )
    return rows


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        raise ValueError("cannot write empty row set")
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def format_value(value: Any) -> str:
    if isinstance(value, bool):
        return str(value).lower()
    if isinstance(value, float):
        return f"{value:.12g}"
    return str(value)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    viable_rows = [row for row in rows if row["viable"]]
    boundary_failures = [row for row in rows if row["boundary_failure"]]
    return {
        "contract": CONTRACT,
        "row_count": len(rows),
        "alpha_min": float(ALPHA_START),
        "alpha_max": float(ALPHA_STOP),
        "alpha_step": float(ALPHA_STEP),
        "alpha_values": [row["alpha"] for row in rows],
        "beta_rule": "beta=alpha-1",
        "recommended_alpha_window": "(1, 3/2)",
        "recommended_alpha_window_lower": 1.0,
        "recommended_alpha_window_upper": 1.5,
        "recommended_window_is_open": True,
        "viable_window_count": len(viable_rows),
        "viable_alpha_values": [row["alpha"] for row in viable_rows],
        "boundary_failures": len(boundary_failures),
        "boundary_failure_rows": [row["row_id"] for row in boundary_failures],
        "bkm_failure_count": sum(not row["bkm_divergence_survives"] for row in rows),
        "concentration_failure_count": sum(not row["concentration_survives"] for row in rows),
        "u1_viscosity_failure_count": sum(not row["u1_viscosity_survives"] for row in rows),
        "nse_consistency_failure_count": sum(not row["nse_consistent"] for row in rows),
        "all_viable_rows_inside_recommended_window": all(
            row["in_recommended_alpha_window"] for row in viable_rows
        ),
        "no_boundary_row_promoted": all(not row["viable"] for row in boundary_failures),
        "clay": False,
        "clay_promoted": False,
        "clay_navier_stokes_promoted": False,
        "complete": False,
        "exit_code": 1,
        "exit_reason": "feasibility window sampled but Clay Navier-Stokes route remains unpromoted",
    }


def markdown_table(rows: list[dict[str, Any]]) -> str:
    headers = (
        "row",
        "alpha",
        "beta",
        "BKM",
        "concentration",
        "u1 viscosity",
        "NSE",
        "in (1,3/2)",
        "viable",
    )
    keys = (
        "row_id",
        "alpha",
        "beta",
        "bkm_divergence_survives",
        "concentration_survives",
        "u1_viscosity_survives",
        "nse_consistent",
        "in_recommended_alpha_window",
        "viable",
    )
    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    for row in rows:
        lines.append("| " + " | ".join(format_value(row[key]) for key in keys) + " |")
    return "\n".join(lines)


def write_report(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    text = "\n".join(
        (
            f"# {CONTRACT}",
            "",
            "Deterministic Sprint129 sampler for the NS viscous feasibility window.",
            "",
            "Formula surface:",
            "",
            "- alpha is sampled on a fixed rational grid across [0.75, 1.75]",
            "- beta = alpha - 1",
            "- recommended_alpha_window = (1, 3/2)",
            "- viable iff BKM, concentration, u1 viscosity, NSE consistency, and open-window gates all hold",
            "- endpoints and exterior samples are recorded as boundary or gate failures",
            "",
            "Summary:",
            "",
            f"- row_count: {format_value(summary['row_count'])}",
            f"- viable_window_count: {format_value(summary['viable_window_count'])}",
            f"- boundary_failures: {format_value(summary['boundary_failures'])}",
            f"- recommended_alpha_window: {summary['recommended_alpha_window']}",
            "- clay_navier_stokes_promoted: "
            f"{format_value(summary['clay_navier_stokes_promoted'])}",
            f"- complete: {format_value(summary['complete'])}",
            f"- exit_code: {format_value(summary['exit_code'])}",
            "",
            "Exit status: 1 because the sampler identifies a model window but does not prove or promote Clay Navier-Stokes.",
            "",
            markdown_table(rows),
            "",
        )
    )
    path.write_text(text, encoding="utf-8")


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

    return int(summary["exit_code"])


if __name__ == "__main__":
    sys.exit(main())
