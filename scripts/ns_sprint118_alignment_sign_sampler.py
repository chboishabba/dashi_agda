#!/usr/bin/env python3
"""Sprint 118 HH-to-low strain alignment sign sampler."""

from __future__ import annotations

import argparse
import csv
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint118_alignment_sign_sampler"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint118_alignment_sign_sampler")
SUMMARY_NAME = "ns_sprint118_alignment_sign_sampler_summary.json"
ROWS_NAME = "ns_sprint118_alignment_sign_sampler_rows.json"
CSV_NAME = "ns_sprint118_alignment_sign_sampler_rows.csv"
REPORT_NAME = "ns_sprint118_alignment_sign_sampler.md"

LAMBDA_VALUES = (-2, -1, 0, 1, 2)
COS2_VALUES = (0.0, 0.25, 0.5, 0.75, 1.0)


@dataclass(frozen=True)
class AlignmentSignRow:
    lambda_value: int
    cos2: float
    contraction: float
    pi_hh_to_l_sign: int
    compressive: bool
    extensive: bool
    aligned: bool
    positive_flux: bool
    classification: str

    def as_row(self) -> dict[str, Any]:
        return asdict(self)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def sign(value: float) -> int:
    if value > 0:
        return 1
    if value < 0:
        return -1
    return 0


def classify(lambda_value: int, cos2: float) -> str:
    if lambda_value < 0 and cos2 > 0:
        return "compressive_aligned_positive_flux"
    if lambda_value > 0:
        return "extensive_nonpositive_flux"
    if lambda_value == 0:
        return "neutral_zero_eigenvalue"
    return "orthogonal_zero_contraction"


def positive_flux(lambda_value: int, cos2: float) -> bool:
    return lambda_value < 0 and cos2 > 0


def build_rows() -> list[AlignmentSignRow]:
    rows: list[AlignmentSignRow] = []
    for lambda_value in LAMBDA_VALUES:
        for cos2 in COS2_VALUES:
            contraction = lambda_value * cos2
            rows.append(
                AlignmentSignRow(
                    lambda_value=lambda_value,
                    cos2=cos2,
                    contraction=contraction,
                    pi_hh_to_l_sign=sign(-contraction),
                    compressive=lambda_value < 0,
                    extensive=lambda_value > 0,
                    aligned=cos2 > 0,
                    positive_flux=positive_flux(lambda_value, cos2),
                    classification=classify(lambda_value, cos2),
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
        "lambda",
        "cos^2",
        "contraction",
        "Pi_HH_to_L sign",
        "compressive",
        "extensive",
        "positive flux",
    )
    keys = (
        "lambda_value",
        "cos2",
        "contraction",
        "pi_hh_to_l_sign",
        "compressive",
        "extensive",
        "positive_flux",
    )
    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    for row in rows:
        lines.append("| " + " | ".join(format_value(row[key]) for key in keys) + " |")
    return "\n".join(lines)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    positive_rows = [row for row in rows if row["positive_flux"]]
    nonpositive_rows = [row for row in rows if not row["positive_flux"]]
    return {
        "contract": CONTRACT,
        "row_count": len(rows),
        "lambda_values": list(LAMBDA_VALUES),
        "cos2_values": list(COS2_VALUES),
        "contraction_formula": "lambda * cos2",
        "pi_hh_to_l_sign_formula": "sign(-contraction)",
        "positive_flux_row_count": len(positive_rows),
        "nonpositive_flux_row_count": len(nonpositive_rows),
        "compressive_aligned_positive_flux_rule": "lambda < 0 and cos2 > 0",
        "extensive_positive_flux_rule": False,
        "pointwise_sign_under_alignment_recorded": True,
        "kinematic_condition_recorded": True,
        "persistent_alignment_existence_closed": False,
        "non_circular_geometric_correlation_source_closed": False,
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
            "Deterministic HH-to-low strain alignment sign sampler.",
            "",
            "Formula surface:",
            "",
            "- contraction = lambda * cos2 for one eigenvector contribution",
            "- Pi_HH_to_L sign = sign(-contraction)",
            "- compressive aligned rows use lambda < 0 and cos2 > 0",
            "- extensive rows use lambda > 0 and are not positive flux rows",
            "",
            f"Pointwise sign under alignment recorded: "
            f"{str(summary['pointwise_sign_under_alignment_recorded']).lower()}.",
            f"Kinematic condition recorded: "
            f"{str(summary['kinematic_condition_recorded']).lower()}.",
            f"Persistent alignment existence closed: "
            f"{str(summary['persistent_alignment_existence_closed']).lower()}.",
            "Non-circular geometric correlation source closed: "
            f"{str(summary['non_circular_geometric_correlation_source_closed']).lower()}.",
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
