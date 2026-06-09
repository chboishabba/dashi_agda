#!/usr/bin/env python3
"""Sprint 119 alignment persistence budget calculator."""

from __future__ import annotations

import argparse
import csv
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint119_alignment_persistence_budget"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint119_alignment_persistence_budget")
SUMMARY_NAME = "ns_sprint119_alignment_persistence_budget_summary.json"
ROWS_NAME = "ns_sprint119_alignment_persistence_budget_rows.json"
CSV_NAME = "ns_sprint119_alignment_persistence_budget_rows.csv"
REPORT_NAME = "ns_sprint119_alignment_persistence_budget.md"

ALIGNMENT_STRENGTH_VALUES = (0.1, 0.25, 0.5, 0.75, 1.0)
DURATION_VALUES = (0.1, 0.25, 0.5, 1.0, 2.0)
ALIGNMENT_INTEGRAL_FORMULA = (
    "alignment integral = integral_0^T compressive_alignment_strength(t) dt"
)
KSTAR_SUPPORT_THRESHOLD = 1.0
CLAY_SUPPORT_THRESHOLD = 2.0


@dataclass(frozen=True)
class AlignmentPersistenceBudgetRow:
    alignment_strength: float
    duration: float
    alignment_integral: float
    kstar_support_threshold: float
    clay_support_threshold: float
    kstar_budget_met: bool
    clay_budget_met: bool
    budget_classification: str

    def as_row(self) -> dict[str, Any]:
        return asdict(self)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def classify_budget(alignment_integral: float) -> str:
    if alignment_integral >= CLAY_SUPPORT_THRESHOLD:
        return "clay_support_budget_met"
    if alignment_integral >= KSTAR_SUPPORT_THRESHOLD:
        return "kstar_support_budget_met"
    return "support_budget_not_met"


def compute_row(
    alignment_strength: float, duration: float
) -> AlignmentPersistenceBudgetRow:
    alignment_integral = alignment_strength * duration
    return AlignmentPersistenceBudgetRow(
        alignment_strength=alignment_strength,
        duration=duration,
        alignment_integral=alignment_integral,
        kstar_support_threshold=KSTAR_SUPPORT_THRESHOLD,
        clay_support_threshold=CLAY_SUPPORT_THRESHOLD,
        kstar_budget_met=alignment_integral >= KSTAR_SUPPORT_THRESHOLD,
        clay_budget_met=alignment_integral >= CLAY_SUPPORT_THRESHOLD,
        budget_classification=classify_budget(alignment_integral),
    )


def build_rows() -> list[AlignmentPersistenceBudgetRow]:
    return [
        compute_row(alignment_strength, duration)
        for alignment_strength in ALIGNMENT_STRENGTH_VALUES
        for duration in DURATION_VALUES
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


def format_value(value: Any) -> str:
    if isinstance(value, bool):
        return str(value).lower()
    if isinstance(value, float):
        return f"{value:.12g}"
    return str(value)


def markdown_table(rows: list[dict[str, Any]]) -> str:
    headers = (
        "strength",
        "duration",
        "alignment integral",
        "kstar budget met",
        "clay budget met",
        "classification",
    )
    keys = (
        "alignment_strength",
        "duration",
        "alignment_integral",
        "kstar_budget_met",
        "clay_budget_met",
        "budget_classification",
    )
    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    for row in rows:
        lines.append("| " + " | ".join(format_value(row[key]) for key in keys) + " |")
    return "\n".join(lines)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    kstar_rows = [row for row in rows if row["kstar_budget_met"]]
    clay_rows = [row for row in rows if row["clay_budget_met"]]
    max_row = max(rows, key=lambda row: row["alignment_integral"])
    min_row = min(rows, key=lambda row: row["alignment_integral"])
    return {
        "contract": CONTRACT,
        "row_count": len(rows),
        "alignment_strength_values": list(ALIGNMENT_STRENGTH_VALUES),
        "duration_values": list(DURATION_VALUES),
        "alignment_integral_formula": ALIGNMENT_INTEGRAL_FORMULA,
        "alignment_integral_model": "strength * duration",
        "kstar_support_threshold": KSTAR_SUPPORT_THRESHOLD,
        "clay_support_threshold": CLAY_SUPPORT_THRESHOLD,
        "kstar_budget_met_count": len(kstar_rows),
        "clay_budget_met_count": len(clay_rows),
        "min_alignment_integral": min_row["alignment_integral"],
        "max_alignment_integral": max_row["alignment_integral"],
        "max_alignment_strength": max_row["alignment_strength"],
        "max_duration": max_row["duration"],
        "non_circular_source_established": False,
        "persistent_alignment_existence_closed": False,
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
            "Deterministic alignment persistence budget calculator.",
            "",
            "Formula surface:",
            "",
            f"- {ALIGNMENT_INTEGRAL_FORMULA}",
            "- constant-strength model: alignment_integral = strength * duration",
            f"- kstar_support_threshold = {format_value(KSTAR_SUPPORT_THRESHOLD)}",
            f"- clay_support_threshold = {format_value(CLAY_SUPPORT_THRESHOLD)}",
            "",
            f"Kstar budget met rows: {summary['kstar_budget_met_count']}.",
            f"Clay budget met rows: {summary['clay_budget_met_count']}.",
            "Non-circular source established: "
            f"{str(summary['non_circular_source_established']).lower()}.",
            "Persistent alignment existence closed: "
            f"{str(summary['persistent_alignment_existence_closed']).lower()}.",
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
