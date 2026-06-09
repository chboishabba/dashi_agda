#!/usr/bin/env python3
"""Sprint 109 NS compact-support source classifier."""

from __future__ import annotations

import argparse
import csv
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint109_compact_support_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint109_compact_support_classifier")
SUMMARY_NAME = "ns_sprint109_compact_support_classifier_summary.json"
ROWS_NAME = "ns_sprint109_compact_support_classifier_rows.json"
CSV_NAME = "ns_sprint109_compact_support_classifier_rows.csv"
REPORT_NAME = "ns_sprint109_compact_support_classifier.md"
ROUTE_DECISION = "FAIL_CLOSED_COMPACT_SUPPORT_SOURCE"

REQUIRED_GATES = (
    "base_exp_smooth_function",
    "boundary_flatness",
    "compact_support_definition",
    "smoothness_across_boundary",
    "non_circular_source",
    "no_forbidden_dependency",
)

FORBIDDEN_DEPENDENCIES = (
    "assumed_bkm_failure",
    "assumed_serrin_failure",
    "assumed_singularity",
    "target_blowup",
    "desired_conclusion",
    "imposed_boundary_flatness",
    "imposed_support_radius",
    "external_forcing",
    "target_kstar_collapse",
    "non_leray_regularization",
)


@dataclass(frozen=True)
class CompactSupportCandidate:
    family_id: str
    family: str
    ansatz: str
    classification: str
    base_exp_smooth_function: bool
    boundary_flatness: bool
    compact_support_definition: bool
    smoothness_across_boundary: bool
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
            "base_exp_smooth_function": self.base_exp_smooth_function,
            "boundary_flatness": self.boundary_flatness,
            "compact_support_definition": self.compact_support_definition,
            "smoothness_across_boundary": self.smoothness_across_boundary,
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


def candidate_families() -> list[CompactSupportCandidate]:
    return [
        CompactSupportCandidate(
            family_id="SEN",
            family="standard_exp_negative_inverse_bump",
            ansatz="use exp(-1/(1-r^2)) on r < 1 and zero outside the boundary",
            classification="classical compact bump without derived Navier-Stokes source role",
            base_exp_smooth_function=True,
            boundary_flatness=True,
            compact_support_definition=True,
            smoothness_across_boundary=True,
            non_circular_source=False,
            forbidden_dependencies=(),
            verdict="reject",
            note=(
                "The exponential inverse profile supplies the usual smooth compact bump, "
                "but it does not derive a non-circular source for the closure argument."
            ),
        ),
        CompactSupportCandidate(
            family_id="PPC",
            family="piecewise_polynomial_cutoff",
            ansatz="patch polynomial pieces to equal one inside and vanish outside a chosen radius",
            classification="finite-order cutoff with boundary flatness not supplied by the construction",
            base_exp_smooth_function=False,
            boundary_flatness=False,
            compact_support_definition=True,
            smoothness_across_boundary=False,
            non_circular_source=False,
            forbidden_dependencies=("imposed_support_radius",),
            verdict="reject",
            note=(
                "The support interval is selected in advance, and a finite polynomial patch "
                "does not provide the required infinite-order flatness across the boundary."
            ),
        ),
        CompactSupportCandidate(
            family_id="MIB",
            family="mollified_indicator_bump",
            ansatz="convolve a ball indicator with a smooth mollifier and use the resulting cutoff",
            classification="regularized indicator with support and boundary behavior imported from inputs",
            base_exp_smooth_function=False,
            boundary_flatness=False,
            compact_support_definition=True,
            smoothness_across_boundary=True,
            non_circular_source=False,
            forbidden_dependencies=("imposed_support_radius", "non_leray_regularization"),
            verdict="reject",
            note=(
                "Mollification gives a smoothened transition, but compact support comes from "
                "the selected indicator radius and the operation is a regularization input."
            ),
        ),
        CompactSupportCandidate(
            family_id="ISC",
            family="imported_schwartz_cutoff",
            ansatz="import a Schwartz cutoff lemma and specialize it to the target compact region",
            classification="external cutoff package without local boundary-source derivation",
            base_exp_smooth_function=True,
            boundary_flatness=True,
            compact_support_definition=True,
            smoothness_across_boundary=True,
            non_circular_source=False,
            forbidden_dependencies=("desired_conclusion",),
            verdict="reject",
            note=(
                "The imported cutoff can meet the analytic shape checks, but its source "
                "use is asserted from the target conclusion rather than derived internally."
            ),
        ),
        CompactSupportCandidate(
            family_id="ICW",
            family="imposed_compact_support_witness",
            ansatz="declare the support radius, boundary flatness, and source witness as hypotheses",
            classification="forbidden compact-support witness by assumption",
            base_exp_smooth_function=True,
            boundary_flatness=True,
            compact_support_definition=True,
            smoothness_across_boundary=True,
            non_circular_source=False,
            forbidden_dependencies=(
                "imposed_boundary_flatness",
                "imposed_support_radius",
                "target_blowup",
                "desired_conclusion",
            ),
            verdict="reject",
            note=(
                "This candidate has the requested formal labels only because the support "
                "radius, boundary flatness, and desired role are placed in the assumptions."
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
        "scope": "deterministic classifier for Navier-Stokes compact-support source candidates",
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
        "sprint109_compact_support_source_closed": False,
        "fail_closed_reason": (
            "No candidate supplies the base exponential smooth function, boundary flatness, "
            "compact-support definition, smoothness across the boundary, and a non-circular "
            "source while avoiding forbidden dependencies."
        ),
        "control_card": {
            "O": "classify candidate compact-support source families",
            "R": "all six gates must pass and forbidden dependencies must be absent",
            "C": "single deterministic Python ledger emitting summary JSON, rows JSON, CSV, and Markdown",
            "S": "five requested candidates evaluated in fixed order",
            "L": "acceptance is conjunction of gate_results",
            "P": ROUTE_DECISION,
            "G": "Clay Navier-Stokes promotion remains false",
            "F": "accepted_source_count is zero because every candidate fails non_circular_source or another required gate",
        },
        "rows": rows,
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 109 Compact-Support Source Classifier",
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
        "base_exp_smooth_function",
        "boundary_flatness",
        "compact_support_definition",
        "smoothness_across_boundary",
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
