#!/usr/bin/env python3
"""Sprint 130 NS viscous-dominance sampler.

This deterministic model-level sampler scans alpha in [1.05, 1.45], sets
beta=alpha-1, and evaluates source-vs-viscous scaling on a fixed rational
tau and nu grid.  The sampled obstruction is that, for every beta > 0 and
nu > 0, the ratio nu * tau^(-3*beta) diverges as tau -> 0.
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


CONTRACT = "ns_sprint130_viscous_dominance_sampler"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint130_viscous_dominance_sampler")
SUMMARY_NAME = "ns_sprint130_viscous_dominance_sampler_summary.json"
ROWS_NAME = "ns_sprint130_viscous_dominance_sampler_rows.json"
CSV_NAME = "ns_sprint130_viscous_dominance_sampler_rows.csv"
REPORT_NAME = "ns_sprint130_viscous_dominance_sampler.md"

ALPHA_START = Fraction(21, 20)
ALPHA_STOP = Fraction(29, 20)
ALPHA_STEP = Fraction(1, 20)
TAU_VALUES = (Fraction(1, 1), Fraction(1, 10), Fraction(1, 100), Fraction(1, 1000))
NU_VALUES = (Fraction(1, 1), Fraction(1, 10), Fraction(1, 100))
FEASIBILITY_WINDOW = (Fraction(1, 1), Fraction(3, 2))


@dataclass(frozen=True)
class ViscousDominanceRow:
    row_id: str
    alpha: float
    alpha_fraction: str
    beta: float
    beta_fraction: str
    tau: float
    tau_fraction: str
    nu: float
    nu_fraction: str
    source_scaling_exponent: str
    source_scaling_value: float
    viscous_scaling_exponent: str
    viscous_scaling_value: float
    ratio_formula: str
    viscous_to_source_ratio: float
    dominance: bool
    asymptotic_dominance: bool
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


def fmt_exponent(value: Fraction) -> str:
    return f"tau^-({fmt_fraction(value)})"


def classify(dominance: bool, asymptotic_dominance: bool) -> str:
    if dominance:
        return "sampled_viscous_dominance"
    if asymptotic_dominance:
        return "finite_tau_source_larger_but_asymptotic_viscous_dominance"
    return "no_viscous_dominance"


def build_rows() -> list[ViscousDominanceRow]:
    rows: list[ViscousDominanceRow] = []
    for alpha in alpha_values():
        beta = alpha - 1
        viscous_power = 1 + 3 * beta
        for tau in TAU_VALUES:
            source_scaling_value = float(tau) ** -1
            viscous_scaling_value = float(tau) ** (-float(viscous_power))
            for nu in NU_VALUES:
                ratio = float(nu) * (float(tau) ** (-3 * float(beta)))
                dominance = ratio > 1
                asymptotic_dominance = beta > 0 and nu > 0
                rows.append(
                    ViscousDominanceRow(
                        row_id=f"r{len(rows):03d}",
                        alpha=float(alpha),
                        alpha_fraction=fmt_fraction(alpha),
                        beta=float(beta),
                        beta_fraction=fmt_fraction(beta),
                        tau=float(tau),
                        tau_fraction=fmt_fraction(tau),
                        nu=float(nu),
                        nu_fraction=fmt_fraction(nu),
                        source_scaling_exponent="tau^-1",
                        source_scaling_value=source_scaling_value,
                        viscous_scaling_exponent=fmt_exponent(viscous_power),
                        viscous_scaling_value=viscous_scaling_value,
                        ratio_formula="nu * tau^(-3*beta)",
                        viscous_to_source_ratio=ratio,
                        dominance=dominance,
                        asymptotic_dominance=asymptotic_dominance,
                        classification=classify(dominance, asymptotic_dominance),
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


def markdown_table(rows: list[dict[str, Any]]) -> str:
    headers = (
        "row",
        "alpha",
        "beta",
        "tau",
        "nu",
        "source",
        "viscous",
        "ratio",
        "dominance",
        "asymptotic",
    )
    keys = (
        "row_id",
        "alpha_fraction",
        "beta_fraction",
        "tau_fraction",
        "nu_fraction",
        "source_scaling_exponent",
        "viscous_scaling_exponent",
        "viscous_to_source_ratio",
        "dominance",
        "asymptotic_dominance",
    )
    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    for row in rows:
        lines.append("| " + " | ".join(format_value(row[key]) for key in keys) + " |")
    return "\n".join(lines)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    dominance_rows = [row for row in rows if row["dominance"]]
    asymptotic_rows = [row for row in rows if row["asymptotic_dominance"]]
    return {
        "contract": CONTRACT,
        "row_count": len(rows),
        "alpha_min": float(ALPHA_START),
        "alpha_max": float(ALPHA_STOP),
        "alpha_step": float(ALPHA_STEP),
        "alpha_values": [float(value) for value in alpha_values()],
        "alpha_fraction_values": [fmt_fraction(value) for value in alpha_values()],
        "beta_rule": "beta=alpha-1",
        "tau_values": [fmt_fraction(value) for value in TAU_VALUES],
        "nu_values": [fmt_fraction(value) for value in NU_VALUES],
        "source_scaling_exponent": "tau^-1",
        "viscous_scaling_exponent": "tau^-(1+3*beta)",
        "ratio_formula": "nu * tau^(-3*beta)",
        "dominance_rule": "ratio > 1",
        "dominance_count": len(dominance_rows),
        "non_dominance_count": len(rows) - len(dominance_rows),
        "asymptotic_dominance_count": len(asymptotic_rows),
        "all_rows_asymptotically_viscous_dominant": all(
            row["asymptotic_dominance"] for row in rows
        ),
        "all_sampled_beta_positive": all(row["beta"] > 0 for row in rows),
        "all_sampled_nu_positive": all(row["nu"] > 0 for row in rows),
        "viscous_dominance_obstruction": True,
        "hou_luo_ns_route_obstructed": True,
        "feasibility_window": "(1, 3/2)",
        "feasibility_window_lower": float(FEASIBILITY_WINDOW[0]),
        "feasibility_window_upper": float(FEASIBILITY_WINDOW[1]),
        "clay": False,
        "clay_promoted": False,
        "clay_navier_stokes_promoted": False,
        "complete": True,
        "exit_code": 0,
        "exit_reason": "viscous dominance obstruction sampled; Clay Navier-Stokes route remains unpromoted",
    }


def write_report(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    text = "\n".join(
        (
            f"# {CONTRACT}",
            "",
            "Deterministic Sprint130 sampler for NS viscous dominance.",
            "",
            "Formula surface:",
            "",
            "- alpha is sampled on a fixed rational grid across [1.05, 1.45]",
            "- feasibility window: 1 < alpha < 3/2",
            "- beta = alpha - 1",
            "- tau samples: 1, 1/10, 1/100, 1/1000",
            "- nu samples: 1, 1/10, 1/100",
            "- source scaling: tau^-1",
            "- viscous scaling: tau^-(1+3*beta)",
            "- viscous/source ratio: nu * tau^(-3*beta)",
            "- sampled dominance iff ratio > 1",
            "- asymptotic dominance holds for every beta > 0 and nu > 0",
            "",
            "Summary:",
            "",
            f"- row_count: {format_value(summary['row_count'])}",
            f"- dominance_count: {format_value(summary['dominance_count'])}",
            f"- non_dominance_count: {format_value(summary['non_dominance_count'])}",
            f"- feasibility_window: {summary['feasibility_window']}",
            "- viscous_dominance_obstruction: "
            f"{format_value(summary['viscous_dominance_obstruction'])}",
            "- hou_luo_ns_route_obstructed: "
            f"{format_value(summary['hou_luo_ns_route_obstructed'])}",
            "- clay_navier_stokes_promoted: "
            f"{format_value(summary['clay_navier_stokes_promoted'])}",
            f"- complete: {format_value(summary['complete'])}",
            f"- exit_code: {format_value(summary['exit_code'])}",
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
