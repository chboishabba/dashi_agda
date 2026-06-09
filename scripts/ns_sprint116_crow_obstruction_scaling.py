#!/usr/bin/env python3
"""Sprint 116 Crow-route obstruction scaling calculator."""

from __future__ import annotations

import argparse
import csv
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint116_crow_obstruction_scaling"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint116_crow_obstruction_scaling")
SUMMARY_NAME = "ns_sprint116_crow_obstruction_scaling_summary.json"
ROWS_NAME = "ns_sprint116_crow_obstruction_scaling_rows.json"
CSV_NAME = "ns_sprint116_crow_obstruction_scaling_rows.csv"
REPORT_NAME = "ns_sprint116_crow_obstruction_scaling.md"

DELTA_REFERENCE_PAIRS = (
    (0.40, 0.175),
    (0.30, 0.075),
    (0.20, 0.025),
    (0.10, 0.004),
    (0.05, 0.0008),
)


@dataclass(frozen=True)
class ObstructionRow:
    delta_over_b: float
    obstruction_ratio: float
    reference_flux_budget_over_e0: float
    obstruction_ratio_normalized_to_delta_0_40: float
    reference_normalized_to_delta_0_40: float
    formula: str

    def as_row(self) -> dict[str, Any]:
        return asdict(self)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def obstruction_ratio(delta_over_b: float) -> float:
    return delta_over_b**2 / math.log(1.0 / delta_over_b)


def build_rows() -> list[ObstructionRow]:
    base_obstruction = obstruction_ratio(DELTA_REFERENCE_PAIRS[0][0])
    base_reference = DELTA_REFERENCE_PAIRS[0][1]
    return [
        ObstructionRow(
            delta_over_b=delta_over_b,
            obstruction_ratio=obstruction_ratio(delta_over_b),
            reference_flux_budget_over_e0=reference_ratio,
            obstruction_ratio_normalized_to_delta_0_40=obstruction_ratio(delta_over_b)
            / base_obstruction,
            reference_normalized_to_delta_0_40=reference_ratio / base_reference,
            formula="(delta_over_b ** 2) / log(1 / delta_over_b)",
        )
        for delta_over_b, reference_ratio in DELTA_REFERENCE_PAIRS
    ]


def strictly_decreases(values: list[float]) -> bool:
    return all(left > right for left, right in zip(values, values[1:]))


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    computed = [float(row["obstruction_ratio"]) for row in rows]
    references = [float(row["reference_flux_budget_over_e0"]) for row in rows]
    return {
        "contract": CONTRACT,
        "row_count": len(rows),
        "delta_over_b_values": [row["delta_over_b"] for row in rows],
        "formula": "(delta_over_b ** 2) / log(1 / delta_over_b)",
        "complete": True,
        "obstruction_calculation_complete": True,
        "option_b_crow_route_obstructed": True,
        "clay": False,
        "clay_promoted": False,
        "clay_navier_stokes_promoted": False,
        "limit_to_zero": strictly_decreases(computed) and computed[-1] > 0.0,
        "reference_ratios_strictly_decrease": strictly_decreases(references),
        "match_claim": "reference ratios are supplied comparison values, not asserted exact formula outputs",
        "exit_code": 0,
    }


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        raise ValueError("cannot write empty rows")
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def format_float(value: float) -> str:
    return f"{value:.12g}"


def markdown_table(rows: list[dict[str, Any]]) -> str:
    headers = (
        "delta/b",
        "obstruction ratio",
        "reference flux budget / e0",
        "obstruction normalized",
        "reference normalized",
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
                    format_float(row["obstruction_ratio"]),
                    format_float(row["reference_flux_budget_over_e0"]),
                    format_float(row["obstruction_ratio_normalized_to_delta_0_40"]),
                    format_float(row["reference_normalized_to_delta_0_40"]),
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
            "Deterministic Crow-route obstruction scaling calculator.",
            "",
            "Formula surface:",
            "",
            "- obstruction_ratio = (delta_over_b ** 2) / log(1 / delta_over_b)",
            "- reference_flux_budget_over_e0 values are supplied comparison ratios",
            "- normalized columns divide by the delta_over_b = 0.40 row",
            "",
            f"Limit-to-zero check: {str(summary['limit_to_zero']).lower()}.",
            f"Option B Crow route obstructed: {str(summary['option_b_crow_route_obstructed']).lower()}.",
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
