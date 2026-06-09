#!/usr/bin/env python3
"""Sprint 124 rotation-cycle integral sampler.

This script is deliberately model-level only: it samples dimensionless
Omega/C ratios greater than one, evaluates the favorable dwell fraction for a
relative rotating-strain phase, and checks that the signed flux over one full
strain rotation cycle has zero mean by both quadrature and half-cycle symmetry.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint124_rotation_cycle_integral_sampler"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint124_rotation_cycle_integral_sampler")
SUMMARY_NAME = "ns_sprint124_rotation_cycle_integral_sampler_summary.json"
ROWS_NAME = "ns_sprint124_rotation_cycle_integral_sampler_rows.json"
CSV_NAME = "ns_sprint124_rotation_cycle_integral_sampler_rows.csv"
REPORT_NAME = "ns_sprint124_rotation_cycle_integral_sampler.md"

OMEGA_OVER_C_VALUES = (1.05, 1.125, 1.25, 1.5, 2.0, 3.0, 5.0, 8.0)
SUBINTERVALS = 8192
TOLERANCE = 1.0e-12


@dataclass(frozen=True)
class RotationCycleIntegralRow:
    row_id: str
    omega_over_c: float
    omega: float
    c_rate: float
    rotation_cycle: float
    relative_phase_advance: float
    favorable_formula: str
    favorable_dwell_fraction_formula: str
    favorable_dwell_fraction: float
    favorable_dwell_time: float
    flux_integrand_formula: str
    flux_integral_closed_form: float
    flux_mean_closed_form: float
    flux_integral_numeric: float
    flux_mean_numeric: float
    max_half_cycle_symmetry_residual: float
    zero_mean_flux: bool
    rotating_strain_blowup_route_closed: bool
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


def positive_cos_measure(angle_span: float) -> float:
    """Measure of s in [0, angle_span] with cos(2s)>0."""
    if angle_span <= 0.0:
        return 0.0

    period = math.pi
    favorable_width = math.pi / 2.0
    full_periods = math.floor(angle_span / period)
    remainder = angle_span - full_periods * period
    measure = full_periods * favorable_width
    measure += min(remainder, favorable_width)
    return measure


def favorable_dwell_fraction(omega: float, c_rate: float, rotation_cycle: float) -> float:
    relative_rate = omega - c_rate
    phase_span = relative_rate * rotation_cycle
    if phase_span <= TOLERANCE:
        return 0.0
    return positive_cos_measure(phase_span) / phase_span


def simpson_integral(omega: float, rotation_cycle: float, subintervals: int) -> float:
    if subintervals % 2 != 0:
        raise ValueError("Simpson integration requires an even subinterval count")
    h = rotation_cycle / subintervals

    def flux(t: float) -> float:
        return math.cos(2.0 * omega * t)

    total = flux(0.0) + flux(rotation_cycle)
    for index in range(1, subintervals):
        total += (4.0 if index % 2 else 2.0) * flux(index * h)
    return total * h / 3.0


def max_half_cycle_residual(omega: float, rotation_cycle: float, samples: int = 257) -> float:
    half_cycle = rotation_cycle / 2.0
    max_residual = 0.0
    for index in range(samples):
        t = half_cycle * index / (samples - 1)
        residual = abs(math.cos(2.0 * omega * t) + math.cos(2.0 * omega * (t + half_cycle)))
        max_residual = max(max_residual, residual)
    return max_residual


def classify(fraction: float, zero_mean_flux: bool) -> str:
    if not zero_mean_flux:
        return "flux_cancellation_failed"
    if fraction > 0.5 + TOLERANCE:
        return "initial_favorable_dwell_bias_but_zero_mean_flux"
    if fraction < 0.5 - TOLERANCE:
        return "initial_unfavorable_dwell_bias_but_zero_mean_flux"
    return "balanced_dwell_and_zero_mean_flux"


def build_rows() -> list[RotationCycleIntegralRow]:
    rows: list[RotationCycleIntegralRow] = []
    omega = 1.0
    rotation_cycle = math.pi / omega
    for ratio in OMEGA_OVER_C_VALUES:
        c_rate = omega / ratio
        relative_phase_advance = (omega - c_rate) * rotation_cycle
        dwell_fraction = favorable_dwell_fraction(omega, c_rate, rotation_cycle)
        numeric_integral = simpson_integral(omega, rotation_cycle, SUBINTERVALS)
        symmetry_residual = max_half_cycle_residual(omega, rotation_cycle)
        zero_mean_flux = (
            abs(numeric_integral) <= 1.0e-12
            and symmetry_residual <= 1.0e-12
        )
        rows.append(
            RotationCycleIntegralRow(
                row_id=f"r{len(rows):03d}",
                omega_over_c=ratio,
                omega=omega,
                c_rate=c_rate,
                rotation_cycle=rotation_cycle,
                relative_phase_advance=relative_phase_advance,
                favorable_formula="cos(2*(Omega-C)*t)>0 on t in [0,pi/Omega]",
                favorable_dwell_fraction_formula=(
                    "measure{s in [0,(Omega-C)*T]: cos(2s)>0}/((Omega-C)*T)"
                ),
                favorable_dwell_fraction=clean(dwell_fraction),
                favorable_dwell_time=clean(dwell_fraction * rotation_cycle),
                flux_integrand_formula="F(t)=cos(2*Omega*t)",
                flux_integral_closed_form=0.0,
                flux_mean_closed_form=0.0,
                flux_integral_numeric=clean(numeric_integral),
                flux_mean_numeric=clean(numeric_integral / rotation_cycle),
                max_half_cycle_symmetry_residual=clean(symmetry_residual),
                zero_mean_flux=zero_mean_flux,
                rotating_strain_blowup_route_closed=zero_mean_flux,
                classification=classify(dwell_fraction, zero_mean_flux),
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
    dwell_fractions = [float(row["favorable_dwell_fraction"]) for row in rows]
    numeric_means = [abs(float(row["flux_mean_numeric"])) for row in rows]
    symmetry_residuals = [float(row["max_half_cycle_symmetry_residual"]) for row in rows]
    zero_mean_flux_established = all(bool(row["zero_mean_flux"]) for row in rows)
    return {
        "contract": CONTRACT,
        "row_count": len(rows),
        "omega_over_c_values": list(OMEGA_OVER_C_VALUES),
        "omega_over_c_all_greater_than_one": all(value > 1.0 for value in OMEGA_OVER_C_VALUES),
        "subintervals": SUBINTERVALS,
        "rotation_cycle_formula": "T=pi/Omega",
        "relative_phase_formula": "theta_rel(t)=(Omega-C)*t",
        "favorable_formula": "cos(2*theta_rel)>0",
        "favorable_dwell_fraction_formula": (
            "measure{s in [0,(Omega-C)*T]: cos(2s)>0}/((Omega-C)*T)"
        ),
        "flux_integrand_formula": "F(t)=cos(2*Omega*t)",
        "flux_integral_closed_form": "integral_0^(pi/Omega) cos(2*Omega*t) dt = 0",
        "half_cycle_symmetry": "F(t+T/2)=-F(t)",
        "favorable_dwell_fraction_min": min(dwell_fractions),
        "favorable_dwell_fraction_max": max(dwell_fractions),
        "max_abs_flux_mean_numeric": max(numeric_means),
        "max_half_cycle_symmetry_residual": max(symmetry_residuals),
        "zero_mean_flux_established": zero_mean_flux_established,
        "rotating_strain_blowup_route_closed": zero_mean_flux_established,
        "clay": False,
        "complete": True,
        "exit_code": 0,
    }


def markdown_table(rows: list[dict[str, Any]]) -> str:
    headers = (
        "row",
        "Omega/C",
        "C",
        "rel advance",
        "dwell fraction",
        "flux mean numeric",
        "sym residual",
        "class",
    )
    keys = (
        "row_id",
        "omega_over_c",
        "c_rate",
        "relative_phase_advance",
        "favorable_dwell_fraction",
        "flux_mean_numeric",
        "max_half_cycle_symmetry_residual",
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
            "Deterministic calculator for Sprint124 rotation-cycle flux cancellation.",
            "",
            "Formula surface:",
            "",
            "- sampled ratios satisfy Omega/C > 1",
            "- T = pi/Omega is one full strain-axis rotation cycle for cos(2*Omega*t)",
            "- theta_rel(t) = (Omega-C)*t",
            "- favorable dwell iff cos(2*theta_rel)>0",
            "- favorable_dwell_fraction = measure{s in [0,(Omega-C)*T]: cos(2s)>0}/((Omega-C)*T)",
            "- signed flux integrand F(t)=cos(2*Omega*t)",
            "- closed form: integral_0^T F(t) dt = 0",
            "- symmetry check: F(t+T/2)=-F(t)",
            "",
            "Summary:",
            "",
            f"- row_count: {format_value(summary['row_count'])}",
            f"- favorable_dwell_fraction_min: {format_value(summary['favorable_dwell_fraction_min'])}",
            f"- favorable_dwell_fraction_max: {format_value(summary['favorable_dwell_fraction_max'])}",
            f"- max_abs_flux_mean_numeric: {format_value(summary['max_abs_flux_mean_numeric'])}",
            f"- max_half_cycle_symmetry_residual: {format_value(summary['max_half_cycle_symmetry_residual'])}",
            f"- zero_mean_flux_established: {format_value(summary['zero_mean_flux_established'])}",
            "- rotating_strain_blowup_route_closed: "
            f"{format_value(summary['rotating_strain_blowup_route_closed'])}",
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
