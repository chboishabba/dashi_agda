#!/usr/bin/env python3
"""Sprint 127 boundary-layer vortex-stretching balance sampler."""

from __future__ import annotations

import argparse
import csv
import json
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint127_boundary_layer_balance_sampler"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint127_boundary_layer_balance_sampler")
SUMMARY_NAME = "ns_sprint127_boundary_layer_balance_sampler_summary.json"
ROWS_NAME = "ns_sprint127_boundary_layer_balance_sampler_rows.json"
CSV_NAME = "ns_sprint127_boundary_layer_balance_sampler_rows.csv"
REPORT_NAME = "ns_sprint127_boundary_layer_balance_sampler.md"

TOLERANCE = Fraction(1, 10**12)

SAMPLE_ROWS = (
    ("hou_luo_compatible_boundary_scaling", Fraction(1), Fraction(0), Fraction(4, 3), Fraction(1, 2), Fraction(1)),
    ("thin_radial_high_viscosity_control", Fraction(1), Fraction(1, 4), Fraction(1), Fraction(3, 2), Fraction(1)),
    ("supercritical_growth_energy_defect", Fraction(3, 2), Fraction(1, 4), Fraction(1, 4), Fraction(1, 2), Fraction(1)),
    ("sub_bkm_bounded_reference", Fraction(3, 4), Fraction(1, 3), Fraction(5, 4), Fraction(1, 2), Fraction(1)),
    ("large_boundary_radius_damped", Fraction(1), Fraction(0), Fraction(4, 3), Fraction(5, 4), Fraction(2)),
    ("strong_stretching_bounded_candidate", Fraction(4, 3), Fraction(2, 3), Fraction(1, 2), Fraction(1, 3), Fraction(1)),
)


@dataclass(frozen=True)
class BalanceRow:
    row_id: str
    label: str
    alpha: float
    beta: float
    gamma: float
    nu: float
    r0: float
    alpha_fraction: str
    beta_fraction: str
    gamma_fraction: str
    nu_fraction: str
    r0_fraction: str
    bkm_candidate: bool
    energy_lhs: float
    energy_rhs: float
    energy_margin: float
    energy_bounded: bool
    omega_over_r0_indicator: float
    viscous_indicator: float
    stretching_beats_viscosity: bool
    balance_compatible: bool
    proof_established: bool
    clay: bool
    classification: str
    reason: str

    def as_row(self) -> dict[str, Any]:
        return asdict(self)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def fraction_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def classify(
    bkm_candidate: bool,
    energy_bounded: bool,
    stretching_beats_viscosity: bool,
) -> tuple[str, str, bool]:
    if bkm_candidate and energy_bounded and stretching_beats_viscosity:
        return (
            "candidate_balance_window",
            "passes BKM threshold, bounded-energy scaling, and stretching-over-viscosity proxy",
            True,
        )

    failed: list[str] = []
    if not bkm_candidate:
        failed.append("BKM threshold alpha >= 1")
    if not energy_bounded:
        failed.append("bounded-energy inequality beta + gamma >= 2*alpha/3")
    if not stretching_beats_viscosity:
        failed.append("omega_over_r0_indicator > viscous_indicator")
    return ("rejected_balance_row", "; ".join(failed), False)


def build_rows() -> list[BalanceRow]:
    rows: list[BalanceRow] = []
    for label, alpha, beta, gamma, nu, r0 in SAMPLE_ROWS:
        bkm_candidate = alpha >= 1
        energy_lhs = beta + gamma
        energy_rhs = Fraction(2, 3) * alpha
        energy_margin = energy_lhs - energy_rhs
        energy_bounded = energy_margin >= -TOLERANCE

        omega_over_r0_indicator = alpha + beta - (r0 - 1)
        viscous_indicator = nu + 2 * beta
        stretching_beats_viscosity = omega_over_r0_indicator > viscous_indicator + TOLERANCE
        classification, reason, balance_compatible = classify(
            bkm_candidate=bkm_candidate,
            energy_bounded=energy_bounded,
            stretching_beats_viscosity=stretching_beats_viscosity,
        )

        rows.append(
            BalanceRow(
                row_id=f"r{len(rows):03d}",
                label=label,
                alpha=float(alpha),
                beta=float(beta),
                gamma=float(gamma),
                nu=float(nu),
                r0=float(r0),
                alpha_fraction=fraction_text(alpha),
                beta_fraction=fraction_text(beta),
                gamma_fraction=fraction_text(gamma),
                nu_fraction=fraction_text(nu),
                r0_fraction=fraction_text(r0),
                bkm_candidate=bkm_candidate,
                energy_lhs=float(energy_lhs),
                energy_rhs=float(energy_rhs),
                energy_margin=float(energy_margin),
                energy_bounded=energy_bounded,
                omega_over_r0_indicator=float(omega_over_r0_indicator),
                viscous_indicator=float(viscous_indicator),
                stretching_beats_viscosity=stretching_beats_viscosity,
                balance_compatible=balance_compatible,
                proof_established=False,
                clay=False,
                classification=classification,
                reason=reason,
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
        "label",
        "alpha",
        "beta",
        "gamma",
        "nu",
        "r0",
        "BKM",
        "energy",
        "stretch",
        "compatible",
    )
    keys = (
        "row_id",
        "label",
        "alpha_fraction",
        "beta_fraction",
        "gamma_fraction",
        "nu_fraction",
        "r0_fraction",
        "bkm_candidate",
        "energy_bounded",
        "stretching_beats_viscosity",
        "balance_compatible",
    )
    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    for row in rows:
        lines.append("| " + " | ".join(format_value(row[key]) for key in keys) + " |")
    return "\n".join(lines)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    compatible_rows = [row for row in rows if row["balance_compatible"]]
    hou_luo_rows = [
        row
        for row in rows
        if row["alpha_fraction"] == "1" and row["beta_fraction"] == "0" and row["gamma_fraction"] == "4/3"
    ]
    return {
        "contract": CONTRACT,
        "row_count": len(rows),
        "balance_compatible_count": len(compatible_rows),
        "bkm_candidate_constraint": "alpha >= 1",
        "energy_bounded_constraint": "beta + gamma >= 2*alpha/3",
        "omega_over_r0_indicator_definition": "alpha + beta - (r0 - 1)",
        "viscous_indicator_definition": "nu + 2*beta",
        "stretching_beats_viscosity_constraint": "omega_over_r0_indicator > viscous_indicator",
        "hou_luo_compatible_scaling_present": bool(hou_luo_rows),
        "hou_luo_compatible_scaling_balance_compatible": any(
            row["balance_compatible"] for row in hou_luo_rows
        ),
        "all_rows_mark_proof_established_false": all(
            row["proof_established"] is False for row in rows
        ),
        "proof_established": False,
        "clay": False,
        "complete": True,
        "exit_code": 0,
    }


def write_report(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    text = "\n".join(
        (
            f"# {CONTRACT}",
            "",
            "Deterministic sampler for axisymmetric boundary vortex-stretching balance.",
            "",
            "Checks:",
            "",
            "- BKM candidate: alpha >= 1",
            "- bounded energy: beta + gamma >= 2*alpha/3",
            "- stretching beats viscosity: omega_over_r0_indicator > viscous_indicator",
            "",
            "Dimensionless proxies:",
            "",
            "- omega_over_r0_indicator = alpha + beta - (r0 - 1)",
            "- viscous_indicator = nu + 2*beta",
            "",
            "The Hou-Luo compatible scaling row alpha=1, beta=0, gamma=4/3 is included.",
            f"Balance-compatible rows: {summary['balance_compatible_count']} of {summary['row_count']}.",
            f"Proof established: {str(summary['proof_established']).lower()}.",
            f"Clay: {str(summary['clay']).lower()}.",
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
