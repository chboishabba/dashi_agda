#!/usr/bin/env python3
"""Sprint 95 NS K-star collapse source matrix."""

from __future__ import annotations

import argparse
import csv
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint95_kstar_collapse_source_matrix"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint95_kstar_collapse_source_matrix")
SUMMARY_NAME = "ns_sprint95_kstar_collapse_source_matrix_summary.json"
ROWS_JSON_NAME = "ns_sprint95_kstar_collapse_source_matrix_rows.json"
CSV_NAME = "ns_sprint95_kstar_collapse_source_matrix.csv"
REPORT_NAME = "ns_sprint95_kstar_collapse_source_matrix.md"

FORBIDDEN_DEPENDENCIES = [
    "clay",
    "target_absorption",
    "desired_conclusion",
    "h1_continuation",
    "theta_preservation",
    "option_c_conditional",
    "conditional_regular",
    "general_data_regular",
    "blowup_construction_assumed",
    "target_blowup",
    "bkm_failure_assumed",
    "serrin_failure_assumed",
    "bkm",
    "serrin",
    "desired_singularity",
    "negated_conditional_criterion_without_mechanism",
]


@dataclass(frozen=True)
class SourceRow:
    source_id: str
    source: str
    supplies_finite_time_kstar_collapse: bool
    supplies_smooth_finite_energy_compatibility: bool
    excludes_conditional_kstar_lower_bound: bool
    extracts_singularity: bool
    forbidden_dependencies: str
    note: str

    @property
    def forbidden_dependency_count(self) -> int:
        return 0 if self.forbidden_dependencies == "none" else len(self.forbidden_dependencies.split(";"))

    @property
    def accepted(self) -> bool:
        return (
            self.supplies_finite_time_kstar_collapse
            and self.supplies_smooth_finite_energy_compatibility
            and self.excludes_conditional_kstar_lower_bound
            and self.extracts_singularity
            and self.forbidden_dependency_count == 0
        )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def rows() -> list[SourceRow]:
    return [
        SourceRow(
            "S87",
            "Sprint87 high-high factorization",
            False,
            False,
            False,
            False,
            "none",
            "Supports conditional absorption estimates only; supplies no finite-time K* collapse mechanism.",
        ),
        SourceRow(
            "S90",
            "Sprint90 local enstrophy route",
            False,
            False,
            False,
            False,
            "none",
            "Records local-enstrophy reduction surfaces but no collapse trajectory.",
        ),
        SourceRow(
            "S94",
            "Sprint94 K-star fork",
            False,
            False,
            False,
            False,
            "none",
            "Records Option B as open and Option C as conditional.",
        ),
        SourceRow(
            "HYP1",
            "low-frequency cascade hypothesis",
            True,
            False,
            False,
            False,
            "none",
            "Names the candidate direction but lacks smooth finite-energy compatibility and singularity extraction.",
        ),
        SourceRow(
            "HYP2",
            "conditional K* lower-bound negation",
            False,
            False,
            True,
            False,
            "negated_conditional_criterion_without_mechanism",
            "Negating the conditional criterion is not a mechanism and cannot be accepted.",
        ),
    ]


def build_summary() -> dict[str, Any]:
    matrix = rows()
    accepted = [row for row in matrix if row.accepted]
    return {
        "contract": CONTRACT,
        "complete": False,
        "fail_closed": True,
        "route_decision": "FAIL_CLOSED",
        "final_decision": "FAIL_CLOSED",
        "promotion_decision": "hold",
        "accepted_source_count": len(accepted),
        "candidate_source_count": len(matrix),
        "clay_navier_stokes_promoted": False,
        "required_residual_gate": "finite-time K* collapse mechanism",
        "required_gates": [
            "dominance",
            "pointwise H1 tail",
            "independent coefficient",
            "same source",
            "finite-time K* collapse",
            "smooth finite-energy compatibility",
            "exclusion of conditional K* lower-bound",
            "finite-time singularity extraction",
        ],
        "forbidden_dependencies": FORBIDDEN_DEPENDENCIES,
        "forbidden_dependency_hits": [
            {
                "source_id": row.source_id,
                "forbidden_dependencies": row.forbidden_dependencies,
            }
            for row in matrix
            if row.forbidden_dependency_count > 0
        ],
        "rows": [
            {**asdict(row), "accepted": row.accepted, "forbidden_dependency_count": row.forbidden_dependency_count}
            for row in matrix
        ],
    }


def write_outputs(out_dir: Path, summary: dict[str, Any]) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    rows_out = summary["rows"]
    (out_dir / SUMMARY_NAME).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out_dir / ROWS_JSON_NAME).write_text(json.dumps(rows_out, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    with (out_dir / CSV_NAME).open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows_out[0].keys()))
        writer.writeheader()
        writer.writerows(rows_out)
    lines = [
        "# NS Sprint 95 K-star Collapse Source Matrix",
        "",
        f"- Contract: `{summary['contract']}`",
        "- Sprint95 K-star collapse source matrix",
        f"- Fail closed: `{summary['fail_closed']}`",
        f"- Accepted source count: `{summary['accepted_source_count']}`",
        f"- Clay Navier-Stokes promoted: `{summary['clay_navier_stokes_promoted']}`",
        f"- Required residual gate: `{summary['required_residual_gate']}`",
        "- Required gates: " + ", ".join(summary["required_gates"]),
        "- Forbidden dependencies: " + ", ".join(summary["forbidden_dependencies"]),
    ]
    (out_dir / REPORT_NAME).write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    args = parse_args()
    summary = build_summary()
    write_outputs(args.out_dir, summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
