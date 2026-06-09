#!/usr/bin/env python3
"""Sprint 107 NS cutoff-partition source classifier."""

from __future__ import annotations

import argparse
import csv
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint107_cutoff_partition_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint107_cutoff_partition_classifier")
SUMMARY_NAME = "ns_sprint107_cutoff_partition_classifier_summary.json"
ROWS_NAME = "ns_sprint107_cutoff_partition_classifier_rows.json"
CSV_NAME = "ns_sprint107_cutoff_partition_classifier_rows.csv"
REPORT_NAME = "ns_sprint107_cutoff_partition_classifier.md"
ROUTE_DECISION = "FAIL_CLOSED_CUTOFF_PARTITION_SOURCE"

REQUIRED_GATES = (
    "radial_bump",
    "annulus_cover",
    "partition_identity",
    "overlap_bound",
    "non_circular_normalization",
    "no_forbidden_dependency",
)

FORBIDDEN_DEPENDENCIES = (
    "assumed_bkm_failure",
    "assumed_serrin_failure",
    "assumed_singularity",
    "target_blowup",
    "desired_conclusion",
    "imposed_cutoff_support",
    "imposed_partition_identity",
    "external_forcing",
    "target_kstar_collapse",
    "non_leray_regularization",
)


@dataclass(frozen=True)
class CutoffPartitionCandidate:
    family_id: str
    family: str
    ansatz: str
    classification: str
    radial_bump: bool
    annulus_cover: bool
    partition_identity: bool
    overlap_bound: bool
    non_circular_normalization: bool
    forbidden_dependencies: tuple[str, ...]
    verdict: str
    note: str

    @property
    def no_forbidden_dependency(self) -> bool:
        return len(self.forbidden_dependencies) == 0

    @property
    def gate_results(self) -> dict[str, bool]:
        return {
            "radial_bump": self.radial_bump,
            "annulus_cover": self.annulus_cover,
            "partition_identity": self.partition_identity,
            "overlap_bound": self.overlap_bound,
            "non_circular_normalization": self.non_circular_normalization,
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


def candidate_families() -> list[CutoffPartitionCandidate]:
    return [
        CutoffPartitionCandidate(
            family_id="SRB",
            family="standard_radial_bump_partition",
            ansatz="use a smooth radial bump and dyadic rescalings to cover Fourier annuli",
            classification="standard partition algebra without independent cutoff-source closure",
            radial_bump=True,
            annulus_cover=True,
            partition_identity=True,
            overlap_bound=True,
            non_circular_normalization=False,
            forbidden_dependencies=("desired_conclusion",),
            verdict="reject",
            note=(
                "The usual radial bump package supplies the formal partition checks, "
                "but its normalization is useful here only after the desired cutoff-source role is assumed."
            ),
        ),
        CutoffPartitionCandidate(
            family_id="CAP",
            family="compact_annulus_partition",
            ansatz="choose compactly supported annular cutoffs with finite overlap",
            classification="annular cover with support imposed as source data",
            radial_bump=True,
            annulus_cover=True,
            partition_identity=False,
            overlap_bound=True,
            non_circular_normalization=False,
            forbidden_dependencies=("imposed_cutoff_support",),
            verdict="reject",
            note=(
                "Compact annuli give a finite-overlap cover, but the exact identity "
                "and source-bearing support are not derived without imposing the cutoff support."
            ),
        ),
        CutoffPartitionCandidate(
            family_id="HKS",
            family="heat_kernel_scale_partition",
            ansatz="use heat-kernel differences to define scale-local smooth cutoffs",
            classification="scale smoothing without compact annular bump partition",
            radial_bump=False,
            annulus_cover=True,
            partition_identity=False,
            overlap_bound=True,
            non_circular_normalization=False,
            forbidden_dependencies=("non_leray_regularization",),
            verdict="reject",
            note=(
                "Heat-kernel differences provide smooth scale localization, but they "
                "are a regularization route rather than a radial bump partition with a closed identity."
            ),
        ),
        CutoffPartitionCandidate(
            family_id="STM",
            family="sharp_to_smooth_mollified_partition",
            ansatz="mollify sharp annular indicators to build a smooth partition",
            classification="mollified annuli with endpoint identity and overlap leakage",
            radial_bump=True,
            annulus_cover=True,
            partition_identity=False,
            overlap_bound=False,
            non_circular_normalization=False,
            forbidden_dependencies=("target_kstar_collapse",),
            verdict="reject",
            note=(
                "Mollification removes sharp edges, but the exact partition identity "
                "and uniform overlap bound are not obtained without tuning to the target shell collapse."
            ),
        ),
        CutoffPartitionCandidate(
            family_id="ICP",
            family="imposed_cutoff_partition",
            ansatz="declare the cutoff supports and partition identity directly",
            classification="forbidden imposed cutoff partition",
            radial_bump=True,
            annulus_cover=True,
            partition_identity=True,
            overlap_bound=True,
            non_circular_normalization=False,
            forbidden_dependencies=(
                "imposed_cutoff_support",
                "imposed_partition_identity",
                "target_blowup",
                "desired_conclusion",
            ),
            verdict="reject",
            note=(
                "The candidate passes formal partition checks only by placing the "
                "support and identity in the hypotheses, so it is circular."
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
        "scope": "deterministic classifier for Navier-Stokes cutoff-partition source candidates",
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
        "sprint107_cutoff_partition_source_closed": False,
        "fail_closed_reason": (
            "No candidate supplies radial bump construction, annulus cover, exact partition identity, "
            "uniform overlap bound, and non-circular normalization while avoiding forbidden dependencies."
        ),
        "control_card": {
            "O": "classify candidate cutoff-partition source families",
            "R": "all six gates must pass and forbidden dependencies must be absent",
            "C": "single deterministic Python ledger emitting summary JSON, rows JSON, CSV, and Markdown",
            "S": "five requested candidates evaluated in fixed order",
            "L": "acceptance is conjunction of gate_results",
            "P": ROUTE_DECISION,
            "G": "Clay Navier-Stokes promotion remains false",
            "F": "accepted_source_count is zero because every candidate fails non_circular_normalization or a prerequisite gate",
        },
        "rows": rows,
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 107 Cutoff-Partition Source Classifier",
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
        "radial_bump",
        "annulus_cover",
        "partition_identity",
        "overlap_bound",
        "non_circular_normalization",
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
