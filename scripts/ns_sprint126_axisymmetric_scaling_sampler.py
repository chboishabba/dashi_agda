#!/usr/bin/env python3
"""Sprint 126 axisymmetric boundary-candidate scaling sampler."""

from __future__ import annotations

import argparse
import csv
import json
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint126_axisymmetric_scaling_sampler"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint126_axisymmetric_scaling_sampler")
SUMMARY_NAME = "ns_sprint126_axisymmetric_scaling_sampler_summary.json"
ROWS_NAME = "ns_sprint126_axisymmetric_scaling_sampler_rows.json"
CSV_NAME = "ns_sprint126_axisymmetric_scaling_sampler_rows.csv"
REPORT_NAME = "ns_sprint126_axisymmetric_scaling_sampler.md"

TOLERANCE = Fraction(1, 10**12)

EXPONENT_ROWS = (
    ("hou_luo_hou_li_boundary_example", Fraction(1), Fraction(0), Fraction(4, 3)),
    ("subcritical_time_amplitude", Fraction(3, 4), Fraction(-1, 4), Fraction(3, 2)),
    ("energy_defect_candidate", Fraction(3, 2), Fraction(1, 2), Fraction(1, 4)),
    ("bkm_subcritical_consistent", Fraction(4, 5), Fraction(-1, 5), Fraction(2)),
    ("nse_inconsistent_reference", Fraction(1), Fraction(1, 5), Fraction(4, 3)),
    ("critical_energy_margin", Fraction(3, 2), Fraction(1, 2), Fraction(1)),
)


@dataclass(frozen=True)
class ScalingRow:
    row_id: str
    label: str
    alpha: float
    beta: float
    gamma: float
    alpha_fraction: str
    beta_fraction: str
    gamma_fraction: str
    nse_consistency_residual: float
    nse_consistent: bool
    energy_lhs: float
    energy_rhs: float
    energy_margin: float
    energy_finite: bool
    bkm_candidate: bool
    compatible: bool
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
    nse_consistent: bool,
    energy_finite: bool,
    bkm_candidate: bool,
) -> tuple[str, str, bool]:
    compatible = nse_consistent and energy_finite and bkm_candidate
    if compatible:
        return (
            "compatible_boundary_candidate",
            "passes NSE scaling, finite-energy, and BKM candidate checks",
            True,
        )
    failed: list[str] = []
    if not nse_consistent:
        failed.append("NSE consistency alpha - beta == 1")
    if not energy_finite:
        failed.append("finite-energy inequality beta + gamma >= 2*alpha/3")
    if not bkm_candidate:
        failed.append("BKM candidate threshold alpha >= 1")
    return ("incompatible_scaling_row", "; ".join(failed), False)


def build_rows() -> list[ScalingRow]:
    rows: list[ScalingRow] = []
    for label, alpha, beta, gamma in EXPONENT_ROWS:
        residual = alpha - beta - 1
        nse_consistent = abs(residual) <= TOLERANCE
        energy_lhs = beta + gamma
        energy_rhs = Fraction(2, 3) * alpha
        energy_margin = energy_lhs - energy_rhs
        energy_finite = energy_margin >= -TOLERANCE
        bkm_candidate = alpha >= 1
        classification, reason, compatible = classify(
            nse_consistent=nse_consistent,
            energy_finite=energy_finite,
            bkm_candidate=bkm_candidate,
        )
        rows.append(
            ScalingRow(
                row_id=f"r{len(rows):03d}",
                label=label,
                alpha=float(alpha),
                beta=float(beta),
                gamma=float(gamma),
                alpha_fraction=fraction_text(alpha),
                beta_fraction=fraction_text(beta),
                gamma_fraction=fraction_text(gamma),
                nse_consistency_residual=float(residual),
                nse_consistent=nse_consistent,
                energy_lhs=float(energy_lhs),
                energy_rhs=float(energy_rhs),
                energy_margin=float(energy_margin),
                energy_finite=energy_finite,
                bkm_candidate=bkm_candidate,
                compatible=compatible,
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
        "NSE",
        "energy finite",
        "BKM",
        "compatible",
        "class",
    )
    keys = (
        "row_id",
        "label",
        "alpha_fraction",
        "beta_fraction",
        "gamma_fraction",
        "nse_consistent",
        "energy_finite",
        "bkm_candidate",
        "compatible",
        "classification",
    )
    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    for row in rows:
        lines.append("| " + " | ".join(format_value(row[key]) for key in keys) + " |")
    return "\n".join(lines)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    compatible_rows = [row for row in rows if row["compatible"]]
    example_rows = [
        row for row in rows
        if row["alpha_fraction"] == "1" and row["beta_fraction"] == "0" and row["gamma_fraction"] == "4/3"
    ]
    return {
        "contract": CONTRACT,
        "row_count": len(rows),
        "compatible_count": len(compatible_rows),
        "compatible_row_count": len(compatible_rows),
        "tolerance": float(TOLERANCE),
        "candidate_family": "Hou-Luo/Hou-Li axisymmetric boundary candidate",
        "nse_consistency_constraint": "alpha - beta == 1",
        "energy_finite_constraint": "beta + gamma >= 2*alpha/3",
        "bkm_candidate_constraint": "alpha >= 1",
        "example_alpha_1_beta_0_gamma_4_over_3_present": bool(example_rows),
        "example_alpha_1_beta_0_gamma_4_over_3_compatible": (
            len(example_rows) == 1 and bool(example_rows[0]["compatible"])
        ),
        "all_compatible_rows_satisfy_constraints": all(
            row["nse_consistent"] and row["energy_finite"] and row["bkm_candidate"]
            for row in compatible_rows
        ),
        "analytic_proof_established": False,
        "clay": False,
        "clay_promoted": False,
        "complete": True,
        "exit_code": 0,
    }


def write_report(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    text = "\n".join(
        (
            f"# {CONTRACT}",
            "",
            "Deterministic exponent sampler for the Hou-Luo/Hou-Li axisymmetric boundary candidate.",
            "",
            "Constraint surface:",
            "",
            "- NSE consistency: alpha - beta == 1 within tolerance",
            "- finite energy: beta + gamma >= 2*alpha/3",
            "- BKM candidate: alpha >= 1",
            "",
            "The row alpha=1, beta=0, gamma=4/3 is included and marked compatible.",
            f"Compatible rows: {summary['compatible_count']} of {summary['row_count']}.",
            f"Analytic proof established: {str(summary['analytic_proof_established']).lower()}.",
            f"Clay promoted: {str(summary['clay']).lower()}.",
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
