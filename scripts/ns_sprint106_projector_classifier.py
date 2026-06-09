#!/usr/bin/env python3
"""Sprint 106 NS projector-source classifier."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint106_projector_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint106_projector_classifier")
SUMMARY_NAME = "ns_sprint106_projector_classifier_summary.json"
ROWS_NAME = "ns_sprint106_projector_classifier_rows.json"
REPORT_NAME = "ns_sprint106_projector_classifier.md"
ROUTE_DECISION = "FAIL_CLOSED_PROJECTOR_SOURCE"

REQUIRED_GATES = (
    "dyadic_partition",
    "multiplier_boundedness",
    "leray_compatibility",
    "divergence_free_commutation",
    "non_circular_construction",
    "no_forbidden_dependency",
)

FORBIDDEN_DEPENDENCIES = (
    "assumed_bkm_failure",
    "assumed_serrin_failure",
    "assumed_singularity",
    "target_blowup",
    "desired_conclusion",
    "imposed_active_shell",
    "imposed_frequency_support",
    "non_leray_regularization",
    "external_forcing",
    "target_kstar_collapse",
)


@dataclass(frozen=True)
class ProjectorCandidate:
    family_id: str
    family: str
    ansatz: str
    classification: str
    dyadic_partition: bool
    multiplier_boundedness: bool
    leray_compatibility: bool
    divergence_free_commutation: bool
    non_circular_construction: bool
    forbidden_dependencies: tuple[str, ...]
    verdict: str
    note: str

    @property
    def no_forbidden_dependency(self) -> bool:
        return len(self.forbidden_dependencies) == 0

    @property
    def gate_results(self) -> dict[str, bool]:
        return {
            "dyadic_partition": self.dyadic_partition,
            "multiplier_boundedness": self.multiplier_boundedness,
            "leray_compatibility": self.leray_compatibility,
            "divergence_free_commutation": self.divergence_free_commutation,
            "non_circular_construction": self.non_circular_construction,
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


def candidate_families() -> list[ProjectorCandidate]:
    return [
        ProjectorCandidate(
            family_id="SDC",
            family="smooth_dyadic_cutoff",
            ansatz="build Littlewood-Paley projectors from a smooth dyadic partition of unity",
            classification="standard dyadic projector without independent active-shell source",
            dyadic_partition=True,
            multiplier_boundedness=True,
            leray_compatibility=True,
            divergence_free_commutation=True,
            non_circular_construction=False,
            forbidden_dependencies=("desired_conclusion",),
            verdict="reject",
            note=(
                "Smooth dyadic cutoffs are valid Leray-compatible multipliers, but "
                "they do not construct the active source without importing the target conclusion."
            ),
        ),
        ProjectorCandidate(
            family_id="SFA",
            family="sharp_frequency_annulus",
            ansatz="project sharply onto a fixed Fourier annulus",
            classification="annular localization with endpoint multiplier obstruction",
            dyadic_partition=True,
            multiplier_boundedness=False,
            leray_compatibility=True,
            divergence_free_commutation=True,
            non_circular_construction=False,
            forbidden_dependencies=("imposed_frequency_support",),
            verdict="reject",
            note=(
                "The annulus names a frequency band, but sharp localization lacks the "
                "required bounded multiplier package and imposes the frequency support."
            ),
        ),
        ProjectorCandidate(
            family_id="HSP",
            family="heat_semigroup_projector",
            ansatz="use heat-flow differences to form scale projectors",
            classification="Leray-compatible smoothing without exact dyadic partition closure",
            dyadic_partition=False,
            multiplier_boundedness=True,
            leray_compatibility=True,
            divergence_free_commutation=True,
            non_circular_construction=False,
            forbidden_dependencies=("non_leray_regularization",),
            verdict="reject",
            note=(
                "Heat semigroup localization is bounded and divergence-free compatible, "
                "but the smoothing route is a regularization surrogate rather than a non-circular projector source."
            ),
        ),
        ProjectorCandidate(
            family_id="LLP",
            family="leray_lp_composed_projector",
            ansatz="compose the Leray projection with smooth Littlewood-Paley cutoffs",
            classification="commuting projector algebra without source mechanism",
            dyadic_partition=True,
            multiplier_boundedness=True,
            leray_compatibility=True,
            divergence_free_commutation=True,
            non_circular_construction=False,
            forbidden_dependencies=("target_kstar_collapse",),
            verdict="reject",
            note=(
                "The Leray and Littlewood-Paley multipliers commute formally, but the "
                "construction becomes useful only after the target shell collapse is supplied."
            ),
        ),
        ProjectorCandidate(
            family_id="IAS",
            family="imposed_active_shell_projector",
            ansatz="select the active shell first and define the projector around it",
            classification="forbidden imposed active-shell source",
            dyadic_partition=True,
            multiplier_boundedness=True,
            leray_compatibility=False,
            divergence_free_commutation=False,
            non_circular_construction=False,
            forbidden_dependencies=(
                "imposed_active_shell",
                "imposed_frequency_support",
                "target_blowup",
                "desired_conclusion",
            ),
            verdict="reject",
            note=(
                "The active shell and supporting frequencies are built into the input, "
                "so the candidate is circular and outside the unforced Leray projector source lane."
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
        "scope": "deterministic classifier for Navier-Stokes projector-source candidates",
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
        "sprint106_projector_source_closed": False,
        "fail_closed_reason": (
            "No candidate supplies a dyadic partition, bounded multiplier package, "
            "Leray compatibility, divergence-free commutation, and non-circular construction "
            "while avoiding forbidden dependencies."
        ),
        "control_card": {
            "O": "classify candidate projector source families",
            "R": "all six gates must pass and forbidden dependencies must be absent",
            "C": "single deterministic Python ledger emitting JSON and Markdown",
            "S": "five requested candidates evaluated in fixed order",
            "L": "acceptance is conjunction of gate_results",
            "P": ROUTE_DECISION,
            "G": "Clay Navier-Stokes promotion remains false",
            "F": "accepted_source_count is zero because every candidate fails non_circular_construction or a prerequisite gate",
        },
        "rows": rows,
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 106 Projector Source Classifier",
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


def write_outputs(out_dir: Path, summary: dict[str, Any]) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / SUMMARY_NAME).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out_dir / ROWS_NAME).write_text(json.dumps(summary["rows"], indent=2, sort_keys=True) + "\n", encoding="utf-8")
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
