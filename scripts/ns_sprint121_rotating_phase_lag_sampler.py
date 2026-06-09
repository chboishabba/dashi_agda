#!/usr/bin/env python3
"""Sprint 121 rotating strain phase-lag sampler."""

from __future__ import annotations

import argparse
import csv
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint121_rotating_phase_lag_sampler"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint121_rotating_phase_lag_sampler")
SUMMARY_NAME = "ns_sprint121_rotating_phase_lag_sampler_summary.json"
ROWS_NAME = "ns_sprint121_rotating_phase_lag_sampler_rows.json"
CSV_NAME = "ns_sprint121_rotating_phase_lag_sampler_rows.csv"
REPORT_NAME = "ns_sprint121_rotating_phase_lag_sampler.md"

OMEGA_VALUES = (0.25, 0.5, 1.0, 2.0, 4.0)
TAU_VALUES = (0.1, 0.25, 0.5, 1.0)
TOLERANCE = 1.0e-12


@dataclass(frozen=True)
class RotatingPhaseLagRow:
    omega: float
    tau: float
    phi_formula: str
    phase_lag: float
    doubled_phase_lag: float
    cos_2_phase_lag: float
    sin_2_phase_lag: float
    positive_flux_window: bool
    amplification_survives: bool
    favorable: bool
    classification: str

    def as_row(self) -> dict[str, Any]:
        return asdict(self)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def clean(value: float) -> float:
    if abs(value) < TOLERANCE:
        return 0.0
    return value


def classify(positive_flux_window: bool, amplification_survives: bool) -> str:
    if positive_flux_window and amplification_survives:
        return "favorable_flux_and_amplification_window"
    if positive_flux_window:
        return "flux_window_without_amplification_survival"
    if amplification_survives:
        return "amplification_survival_without_positive_flux_window"
    return "unfavorable_phase_lag_window"


def build_rows() -> list[RotatingPhaseLagRow]:
    rows: list[RotatingPhaseLagRow] = []
    for omega in OMEGA_VALUES:
        for tau in TAU_VALUES:
            phase_lag = omega * tau
            doubled_phase_lag = 2.0 * phase_lag
            cos_2_phase_lag = clean(math.cos(doubled_phase_lag))
            sin_2_phase_lag = clean(math.sin(doubled_phase_lag))
            positive_flux_window = cos_2_phase_lag > TOLERANCE
            amplification_survives = sin_2_phase_lag > TOLERANCE
            favorable = positive_flux_window and amplification_survives
            rows.append(
                RotatingPhaseLagRow(
                    omega=omega,
                    tau=tau,
                    phi_formula="phi(t)=omega*t",
                    phase_lag=phase_lag,
                    doubled_phase_lag=doubled_phase_lag,
                    cos_2_phase_lag=cos_2_phase_lag,
                    sin_2_phase_lag=sin_2_phase_lag,
                    positive_flux_window=positive_flux_window,
                    amplification_survives=amplification_survives,
                    favorable=favorable,
                    classification=classify(positive_flux_window, amplification_survives),
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
        "omega",
        "tau",
        "phase lag",
        "cos(2 lag)",
        "sin(2 lag)",
        "positive flux",
        "amplification survives",
        "favorable",
    )
    keys = (
        "omega",
        "tau",
        "phase_lag",
        "cos_2_phase_lag",
        "sin_2_phase_lag",
        "positive_flux_window",
        "amplification_survives",
        "favorable",
    )
    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    for row in rows:
        lines.append("| " + " | ".join(format_value(row[key]) for key in keys) + " |")
    return "\n".join(lines)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    favorable_rows = [row for row in rows if row["favorable"]]
    return {
        "contract": CONTRACT,
        "row_count": len(rows),
        "omega_values": list(OMEGA_VALUES),
        "tau_values": list(TAU_VALUES),
        "phi_formula": "phi(t)=omega*t",
        "packet_memory_lag": "tau",
        "phase_lag_formula": "omega*tau",
        "positive_flux_window_formula": "cos(2*phase_lag)>0",
        "amplification_survives_formula": "sin(2*phase_lag)>0",
        "favorable_rule": "positive_flux_window and amplification_survives",
        "favorable_row_count": len(favorable_rows),
        "favorable_rows_are_partial_grid_only": len(favorable_rows) < len(rows),
        "only_some_parameter_rows_are_favorable": 0 < len(favorable_rows) < len(rows),
        "non_circular_persistence_source_established": False,
        "non_circular_persistence_established": False,
        "rotating_strain_decorrelation_mechanism_closed": False,
        "clay": False,
        "complete": True,
        "exit_code": 0,
    }


def write_report(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    text = "\n".join(
        (
            f"# {CONTRACT}",
            "",
            "Deterministic sampler for rotating strain phase-lag.",
            "",
            "Formula surface:",
            "",
            "- phi(t)=omega*t",
            "- packet memory lag = tau",
            "- phase_lag = omega*tau",
            "- positive_flux_window iff cos(2*phase_lag)>0",
            "- amplification_survives iff sin(2*phase_lag)>0",
            "- favorable iff both gates hold",
            "",
            "Summary:",
            "",
            f"- favorable_row_count: {format_value(summary['favorable_row_count'])}",
            "- only_some_parameter_rows_are_favorable: "
            f"{format_value(summary['only_some_parameter_rows_are_favorable'])}",
            "- non_circular_persistence_established: "
            f"{format_value(summary['non_circular_persistence_established'])}",
            "- rotating_strain_decorrelation_mechanism_closed: "
            f"{format_value(summary['rotating_strain_decorrelation_mechanism_closed'])}",
            f"- clay: {format_value(summary['clay'])}",
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
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
