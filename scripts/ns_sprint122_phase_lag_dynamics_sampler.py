#!/usr/bin/env python3
"""Sprint 122 rotating phase-lag dynamics sampler."""

from __future__ import annotations

import argparse
import csv
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint122_phase_lag_dynamics_sampler"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint122_phase_lag_dynamics_sampler")
SUMMARY_NAME = "ns_sprint122_phase_lag_dynamics_sampler_summary.json"
ROWS_NAME = "ns_sprint122_phase_lag_dynamics_sampler_rows.json"
CSV_NAME = "ns_sprint122_phase_lag_dynamics_sampler_rows.csv"
REPORT_NAME = "ns_sprint122_phase_lag_dynamics_sampler.md"

OMEGA_VALUES = (0.5, 1.0, 1.5, 2.0)
DRIFT_VALUES = (0.0, 0.125, 0.25, 0.5)
DAMPING_VALUES = (0.0, 0.05, 0.1)
DURATION_VALUES = (1.0, 2.0, 4.0)
THETA0_VALUES = (0.0, math.pi / 16.0, math.pi / 8.0, math.pi / 4.0)
SAMPLE_COUNT = 257
TOLERANCE = 1.0e-12


@dataclass(frozen=True)
class PhaseLagDynamicsRow:
    row_id: str
    omega: float
    drift: float
    damping: float
    duration: float
    theta0: float
    theta_formula: str
    effective_rate: float
    sample_count: int
    favorable_sample_count: int
    favorable_duration_fraction: float
    favorable_duration_integral: float
    endpoint_theta: float
    endpoint_cos_2_theta: float
    endpoint_sin_2_theta: float
    favorable_dynamic: bool
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


def is_favorable(theta: float) -> bool:
    doubled = 2.0 * theta
    return math.cos(doubled) > TOLERANCE and math.sin(doubled) > TOLERANCE


def theta_at(theta0: float, omega: float, drift: float, damping: float, t: float) -> float:
    return theta0 + omega * t - drift * t - damping * t


def favorable_fraction(
    theta0: float,
    omega: float,
    drift: float,
    damping: float,
    duration: float,
) -> tuple[int, float]:
    favorable_samples = 0
    for index in range(SAMPLE_COUNT):
        t = duration * index / (SAMPLE_COUNT - 1)
        if is_favorable(theta_at(theta0, omega, drift, damping, t)):
            favorable_samples += 1
    return favorable_samples, favorable_samples / SAMPLE_COUNT


def classify(fraction: float) -> str:
    if fraction >= 0.75:
        return "high_favorable_duration"
    if fraction > 0.0:
        return "partial_favorable_duration"
    return "no_favorable_duration"


def build_rows() -> list[PhaseLagDynamicsRow]:
    rows: list[PhaseLagDynamicsRow] = []
    for omega in OMEGA_VALUES:
        for drift in DRIFT_VALUES:
            for damping in DAMPING_VALUES:
                for duration in DURATION_VALUES:
                    for theta0 in THETA0_VALUES:
                        favorable_samples, fraction = favorable_fraction(
                            theta0=theta0,
                            omega=omega,
                            drift=drift,
                            damping=damping,
                            duration=duration,
                        )
                        endpoint_theta = theta_at(theta0, omega, drift, damping, duration)
                        doubled_endpoint = 2.0 * endpoint_theta
                        effective_rate = omega - drift - damping
                        rows.append(
                            PhaseLagDynamicsRow(
                                row_id=f"r{len(rows):04d}",
                                omega=omega,
                                drift=drift,
                                damping=damping,
                                duration=duration,
                                theta0=theta0,
                                theta_formula="theta(t)=theta0+omega*t-drift*t-damping*t",
                                effective_rate=effective_rate,
                                sample_count=SAMPLE_COUNT,
                                favorable_sample_count=favorable_samples,
                                favorable_duration_fraction=fraction,
                                favorable_duration_integral=fraction * duration,
                                endpoint_theta=endpoint_theta,
                                endpoint_cos_2_theta=clean(math.cos(doubled_endpoint)),
                                endpoint_sin_2_theta=clean(math.sin(doubled_endpoint)),
                                favorable_dynamic=fraction > 0.0,
                                classification=classify(fraction),
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
    favorable_rows = [row for row in rows if row["favorable_dynamic"]]
    fractions = [float(row["favorable_duration_fraction"]) for row in rows]
    integrals = [float(row["favorable_duration_integral"]) for row in rows]
    return {
        "contract": CONTRACT,
        "row_count": len(rows),
        "omega_values": list(OMEGA_VALUES),
        "drift_values": list(DRIFT_VALUES),
        "damping_values": list(DAMPING_VALUES),
        "duration_values": list(DURATION_VALUES),
        "theta0_values": list(THETA0_VALUES),
        "theta_formula": "theta(t)=theta0+omega*t-drift*t-damping*t",
        "favorable_rule": "cos(2*theta)>0 and sin(2*theta)>0",
        "sample_count_per_row": SAMPLE_COUNT,
        "favorable_dynamic_rows_count": len(favorable_rows),
        "favorable_duration_fraction_min": min(fractions),
        "favorable_duration_fraction_max": max(fractions),
        "favorable_duration_integral_min": min(integrals),
        "favorable_duration_integral_max": max(integrals),
        "non_circular_dynamic_bound_established": False,
        "persistence_bound_closed": False,
        "clay": False,
        "complete": True,
        "exit_code": 0,
    }


def markdown_table(rows: list[dict[str, Any]]) -> str:
    headers = (
        "row",
        "omega",
        "drift",
        "damping",
        "duration",
        "theta0",
        "fraction",
        "integral",
        "class",
    )
    keys = (
        "row_id",
        "omega",
        "drift",
        "damping",
        "duration",
        "theta0",
        "favorable_duration_fraction",
        "favorable_duration_integral",
        "classification",
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
            "Deterministic sampler for rotating phase-lag dynamics.",
            "",
            "Formula surface:",
            "",
            "- theta(t)=theta0+omega*t-drift*t-damping*t",
            "- favorable iff cos(2*theta)>0 and sin(2*theta)>0",
            "- favorable_duration_fraction is favorable samples divided by total samples",
            "- favorable_duration_integral is fraction times duration",
            "",
            "Summary:",
            "",
            "- favorable_dynamic_rows_count: "
            f"{format_value(summary['favorable_dynamic_rows_count'])}",
            "- non_circular_dynamic_bound_established: "
            f"{format_value(summary['non_circular_dynamic_bound_established'])}",
            "- persistence_bound_closed: "
            f"{format_value(summary['persistence_bound_closed'])}",
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
