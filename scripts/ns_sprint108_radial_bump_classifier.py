#!/usr/bin/env python3
"""Sprint 108 NS radial-bump source classifier."""

from __future__ import annotations

import argparse
import csv
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint108_radial_bump_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint108_radial_bump_classifier")
SUMMARY_NAME = "ns_sprint108_radial_bump_classifier_summary.json"
ROWS_NAME = "ns_sprint108_radial_bump_classifier_rows.json"
CSV_NAME = "ns_sprint108_radial_bump_classifier_rows.csv"
REPORT_NAME = "ns_sprint108_radial_bump_classifier.md"
ROUTE_DECISION = "FAIL_CLOSED_RADIAL_BUMP_SOURCE"

REQUIRED_GATES = (
    "smooth_compact_support",
    "radial_profile",
    "nonnegative_bump",
    "annular_difference",
    "non_circular_source",
    "no_forbidden_dependency",
)

FORBIDDEN_DEPENDENCIES = (
    "assumed_bkm_failure",
    "assumed_serrin_failure",
    "assumed_singularity",
    "target_blowup",
    "desired_conclusion",
    "imposed_profile_support",
    "imposed_partition_identity",
    "external_forcing",
    "target_kstar_collapse",
    "non_leray_regularization",
)


@dataclass(frozen=True)
class RadialBumpCandidate:
    family_id: str
    family: str
    ansatz: str
    classification: str
    smooth_compact_support: bool
    radial_profile: bool
    nonnegative_bump: bool
    annular_difference: bool
    non_circular_source: bool
    forbidden_dependencies: tuple[str, ...]
    verdict: str
    note: str

    @property
    def no_forbidden_dependency(self) -> bool:
        return len(self.forbidden_dependencies) == 0

    @property
    def gate_results(self) -> dict[str, bool]:
        return {
            "smooth_compact_support": self.smooth_compact_support,
            "radial_profile": self.radial_profile,
            "nonnegative_bump": self.nonnegative_bump,
            "annular_difference": self.annular_difference,
            "non_circular_source": self.non_circular_source,
            "no_forbidden_dependency": self.no_forbidden_dependency,
        }

    @property
    def accepted(self) -> bool:
        return all(self.gate_results.values())

    def row(self) -> dict[str, Any]:
        payload = asdict(self)
        payload["forbidden_dependencies"] = (
            "none" if not self.forbidden_dependencies else ";".join(self.forbidden_dependencies)
        )
        payload["no_forbidden_dependency"] = self.no_forbidden_dependency
        payload["gate_results"] = self.gate_results
        payload["failed_gates"] = [
            gate for gate, passed in self.gate_results.items() if not passed
        ]
        payload["accepted"] = self.accepted
        return payload


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def candidate_families() -> list[RadialBumpCandidate]:
    return [
        RadialBumpCandidate(
            family_id="SEC",
            family="standard_exp_cutoff_bump",
            ansatz="use exp(-1/(1-r^2)) inside the unit ball and zero outside",
            classification="standard smooth compact radial bump without annular source derivation",
            smooth_compact_support=True,
            radial_profile=True,
            nonnegative_bump=True,
            annular_difference=False,
            non_circular_source=False,
            forbidden_dependencies=(),
            verdict="reject",
            note=(
                "The classical bump has smooth compact support and positivity, but it is "
                "only a local profile; it does not derive the annular difference source."
            ),
        ),
        RadialBumpCandidate(
            family_id="MBI",
            family="mollified_ball_indicator",
            ansatz="mollify a sharp radial ball indicator to obtain a smooth cutoff",
            classification="smoothened indicator with support inherited from the imposed ball",
            smooth_compact_support=True,
            radial_profile=True,
            nonnegative_bump=True,
            annular_difference=False,
            non_circular_source=False,
            forbidden_dependencies=("imposed_profile_support",),
            verdict="reject",
            note=(
                "Mollification supplies smoothness only after the support geometry is placed "
                "in the input, and the annular difference is not a derived source."
            ),
        ),
        RadialBumpCandidate(
            family_id="GTB",
            family="gaussian_truncation_bump",
            ansatz="multiply a Gaussian profile by a compact radial cutoff",
            classification="truncated heat profile with compactness from an external cutoff",
            smooth_compact_support=True,
            radial_profile=True,
            nonnegative_bump=True,
            annular_difference=False,
            non_circular_source=False,
            forbidden_dependencies=("non_leray_regularization",),
            verdict="reject",
            note=(
                "The Gaussian profile is regularizing data, and compact support comes from "
                "a truncation rather than a non-circular Leray source."
            ),
        ),
        RadialBumpCandidate(
            family_id="IPB",
            family="imported_partition_bump",
            ansatz="import a Littlewood-Paley partition bump and reuse its annular algebra",
            classification="partition artifact without independent radial-bump source closure",
            smooth_compact_support=True,
            radial_profile=True,
            nonnegative_bump=False,
            annular_difference=True,
            non_circular_source=False,
            forbidden_dependencies=("imposed_partition_identity", "desired_conclusion"),
            verdict="reject",
            note=(
                "The imported partition can express annular differences, but its identity "
                "and source role are assumed rather than derived for this classifier."
            ),
        ),
        RadialBumpCandidate(
            family_id="IRP",
            family="imposed_radial_profile",
            ansatz="declare the desired radial profile, support, and annular shell directly",
            classification="forbidden imposed profile source",
            smooth_compact_support=True,
            radial_profile=True,
            nonnegative_bump=True,
            annular_difference=True,
            non_circular_source=False,
            forbidden_dependencies=(
                "imposed_profile_support",
                "imposed_partition_identity",
                "target_blowup",
                "desired_conclusion",
            ),
            verdict="reject",
            note=(
                "This candidate passes the formal shape checks only by including the "
                "desired profile support and annular identity in the hypotheses."
            ),
        ),
    ]


def build_summary() -> dict[str, Any]:
    rows = [candidate.row() for candidate in candidate_families()]
    accepted = [row for row in rows if row["accepted"]]
    return {
        "contract": CONTRACT,
        "complete": False,
        "proof_claimed": False,
        "scope": "deterministic classifier for Navier-Stokes radial-bump source candidates",
        "fail_closed": True,
        "route_decision": ROUTE_DECISION,
        "final_decision": ROUTE_DECISION,
        "accepted_source_count": len(accepted),
        "candidate_family_count": len(rows),
        "required_gates": list(REQUIRED_GATES),
        "forbidden_dependencies": list(FORBIDDEN_DEPENDENCIES),
        "accepted_families": [row["family"] for row in accepted],
        "rejected_families": [row["family"] for row in rows if not row["accepted"]],
        "option_b_closed": False,
        "clay_navier_stokes_promoted": False,
        "clay": False,
        "sprint108_radial_bump_source_closed": False,
        "fail_closed_reason": (
            "No candidate supplies smooth compact support, a radial profile, "
            "nonnegative bump data, annular difference, and a non-circular source "
            "while avoiding forbidden dependencies."
        ),
        "control_card": {
            "O": "classify candidate radial-bump source families",
            "R": "all six gates must pass and forbidden dependencies must be absent",
            "C": "single deterministic Python ledger emitting summary JSON, rows JSON, CSV, and Markdown",
            "S": "five requested candidates evaluated in fixed order",
            "L": "acceptance is conjunction of gate_results",
            "P": ROUTE_DECISION,
            "G": "Clay Navier-Stokes promotion remains false",
            "F": "accepted_source_count is zero because every candidate fails non_circular_source or a prerequisite gate",
        },
        "rows": rows,
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 108 Radial-Bump Source Classifier",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Fail closed: `{str(summary['fail_closed']).lower()}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Accepted source count: `{summary['accepted_source_count']}`",
        f"- Candidate family count: `{summary['candidate_family_count']}`",
        f"- Clay Navier-Stokes promoted: `{str(summary['clay_navier_stokes_promoted']).lower()}`",
        f"- Clay: `{str(summary['clay']).lower()}`",
        "- Required gates: " + ", ".join(f"`{gate}`" for gate in summary["required_gates"]),
        "- Forbidden dependencies: "
        + ", ".join(f"`{item}`" for item in summary["forbidden_dependencies"]),
        "",
        "| Family | Accepted | Failed gates | Forbidden dependencies | Note |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in summary["rows"]:
        failed = "none" if not row["failed_gates"] else ", ".join(f"`{gate}`" for gate in row["failed_gates"])
        lines.append(
            f"| `{row['family']}` | `{str(row['accepted']).lower()}` | {failed} | `{row['forbidden_dependencies']}` | {row['note']} |"
        )
    lines.extend(["", summary["fail_closed_reason"]])
    return "\n".join(lines) + "\n"


def write_csv(out_dir: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = [
        "family_id",
        "family",
        "ansatz",
        "classification",
        "smooth_compact_support",
        "radial_profile",
        "nonnegative_bump",
        "annular_difference",
        "non_circular_source",
        "no_forbidden_dependency",
        "forbidden_dependencies",
        "failed_gates",
        "accepted",
        "verdict",
        "note",
    ]
    with (out_dir / CSV_NAME).open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            csv_row = {key: row[key] for key in fieldnames}
            csv_row["failed_gates"] = "none" if not row["failed_gates"] else ";".join(row["failed_gates"])
            writer.writerow(csv_row)


def write_outputs(out_dir: Path, summary: dict[str, Any]) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / SUMMARY_NAME).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out_dir / ROWS_NAME).write_text(json.dumps(summary["rows"], indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_csv(out_dir, summary["rows"])
    (out_dir / REPORT_NAME).write_text(render_markdown(summary), encoding="utf-8")


def main() -> int:
    args = parse_args()
    summary = build_summary()
    out_dir = args.out_dir if args.out_dir.is_absolute() else args.repo_root / args.out_dir
    write_outputs(out_dir, summary)
    print(json.dumps({key: summary[key] for key in ("contract", "route_decision", "accepted_source_count", "clay")}, sort_keys=True))
    return 1 if summary["fail_closed"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
