#!/usr/bin/env python3
"""Sprint 114 NS reconnection-window lower-bound candidate classifier."""

from __future__ import annotations

import argparse
import csv
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint114_reconnection_window_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint114_reconnection_window_classifier")
SUMMARY_NAME = "ns_sprint114_reconnection_window_classifier_summary.json"
ROWS_NAME = "ns_sprint114_reconnection_window_classifier_rows.json"
CSV_NAME = "ns_sprint114_reconnection_window_classifier_rows.csv"
REPORT_NAME = "ns_sprint114_reconnection_window_classifier.md"
ROUTE_DECISION = "FAIL_CLOSED_RECONNECTION_WINDOW_LOWER_BOUND_SOURCE"

REQUIRED_GATES = (
    "thin_core_crow_dominance",
    "elliptic_backreaction_bound",
    "reconnection_window_lower_bound",
    "viscous_decay_window",
    "nonlinear_deformation_control",
    "positive_flux_accumulation",
    "kstar_collapse_threshold",
    "no_forbidden_dependency",
)

FORBIDDEN_DEPENDENCIES = (
    "assumed_blowup",
    "imposed_flux_surplus",
    "imposed_reconnection_duration",
    "hidden_regular_continuation",
    "numerical_only_evidence",
    "external_forcing",
    "target_kstar_collapse",
)


@dataclass(frozen=True)
class ReconnectionWindowCandidate:
    family_id: str
    family: str
    ansatz: str
    classification: str
    thin_core_crow_dominance: bool
    elliptic_backreaction_bound: bool
    reconnection_window_lower_bound: bool
    viscous_decay_window: bool
    nonlinear_deformation_control: bool
    positive_flux_accumulation: bool
    kstar_collapse_threshold: bool
    forbidden_dependencies: tuple[str, ...]
    verdict: str
    concrete_rejection_reason: str

    @property
    def no_forbidden_dependency(self) -> bool:
        return len(self.forbidden_dependencies) == 0

    @property
    def gate_results(self) -> dict[str, bool]:
        return {
            "thin_core_crow_dominance": self.thin_core_crow_dominance,
            "elliptic_backreaction_bound": self.elliptic_backreaction_bound,
            "reconnection_window_lower_bound": self.reconnection_window_lower_bound,
            "viscous_decay_window": self.viscous_decay_window,
            "nonlinear_deformation_control": self.nonlinear_deformation_control,
            "positive_flux_accumulation": self.positive_flux_accumulation,
            "kstar_collapse_threshold": self.kstar_collapse_threshold,
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


def candidate_families() -> list[ReconnectionWindowCandidate]:
    return [
        ReconnectionWindowCandidate(
            family_id="TCR",
            family="thin_core_rate_correction",
            ansatz=(
                "sharpen the thin-core Crow-over-elliptic initial rate comparison "
                "and use the corrected sign as the reconnection-window source"
            ),
            classification=(
                "partial supporting rate correction; supplies thin-core dominance "
                "only at the rate-comparison level"
            ),
            thin_core_crow_dominance=True,
            elliptic_backreaction_bound=False,
            reconnection_window_lower_bound=False,
            viscous_decay_window=False,
            nonlinear_deformation_control=False,
            positive_flux_accumulation=False,
            kstar_collapse_threshold=False,
            forbidden_dependencies=(),
            verdict="partial",
            concrete_rejection_reason=(
                "The thin-core rate correction is admissible supporting evidence "
                "for initial Crow dominance, but it does not derive elliptic "
                "backreaction control, a viscous nonlinear window, positive flux "
                "accumulation, or a k-star collapse threshold."
            ),
        ),
        ReconnectionWindowCandidate(
            family_id="EBB",
            family="elliptic_backreaction_bound",
            ansatz=(
                "bound elliptic backreaction against the corrected thin-core Crow "
                "rate and promote the comparison to a reconnection interval"
            ),
            classification=(
                "partial supporting elliptic bound; does not close a lower bound "
                "for the reconnection window"
            ),
            thin_core_crow_dominance=True,
            elliptic_backreaction_bound=True,
            reconnection_window_lower_bound=False,
            viscous_decay_window=False,
            nonlinear_deformation_control=False,
            positive_flux_accumulation=False,
            kstar_collapse_threshold=False,
            forbidden_dependencies=(),
            verdict="partial",
            concrete_rejection_reason=(
                "The elliptic backreaction estimate can support the initial "
                "comparison, but it is not a derived unforced NSE lower bound on "
                "reconnection duration and does not control nonlinear deformation "
                "or flux accumulation through collapse."
            ),
        ),
        ReconnectionWindowCandidate(
            family_id="LRE",
            family="linear_reconnection_episode",
            ansatz=(
                "use a linear Crow episode with formal viscous damping to infer "
                "the nonlinear reconnection window"
            ),
            classification="linear proxy without nonlinear reconnection-window closure",
            thin_core_crow_dominance=True,
            elliptic_backreaction_bound=False,
            reconnection_window_lower_bound=False,
            viscous_decay_window=True,
            nonlinear_deformation_control=False,
            positive_flux_accumulation=False,
            kstar_collapse_threshold=False,
            forbidden_dependencies=("imposed_reconnection_duration",),
            verdict="reject",
            concrete_rejection_reason=(
                "The linear episode supplies a formal decay scale but inserts the "
                "reconnection duration and omits elliptic backreaction, nonlinear "
                "deformation, positive flux accumulation, and k-star threshold "
                "closure."
            ),
        ),
        ReconnectionWindowCandidate(
            family_id="SRC",
            family="short_time_regular_continuation",
            ansatz=(
                "propagate smooth thin-core data by local regularity and read the "
                "existence interval as the reconnection window"
            ),
            classification="regular continuation proxy with a forbidden hidden dependency",
            thin_core_crow_dominance=True,
            elliptic_backreaction_bound=True,
            reconnection_window_lower_bound=False,
            viscous_decay_window=False,
            nonlinear_deformation_control=True,
            positive_flux_accumulation=False,
            kstar_collapse_threshold=False,
            forbidden_dependencies=("hidden_regular_continuation",),
            verdict="reject",
            concrete_rejection_reason=(
                "Local smooth continuation controls deformation only by assuming a "
                "regular interval already exists, and it does not derive the "
                "reconnection-window lower bound or the positive flux and k-star "
                "collapse gates."
            ),
        ),
        ReconnectionWindowCandidate(
            family_id="PFA",
            family="positive_flux_surplus_inserted",
            ansatz=(
                "insert a positive flux surplus across a desired reconnection "
                "interval and infer collapse from that surplus"
            ),
            classification="forbidden insertion of the flux conclusion",
            thin_core_crow_dominance=False,
            elliptic_backreaction_bound=False,
            reconnection_window_lower_bound=False,
            viscous_decay_window=False,
            nonlinear_deformation_control=False,
            positive_flux_accumulation=True,
            kstar_collapse_threshold=True,
            forbidden_dependencies=("imposed_flux_surplus", "imposed_reconnection_duration"),
            verdict="reject",
            concrete_rejection_reason=(
                "The candidate assumes the flux surplus and duration that the "
                "classifier is meant to source, so the apparent k-star threshold is "
                "not derived from unforced NSE estimates."
            ),
        ),
        ReconnectionWindowCandidate(
            family_id="NRE",
            family="numerical_reconnection_episode",
            ansatz="promote simulated reconnection timing as evidence for the lower bound",
            classification="computational episode without analytic lower-bound proof",
            thin_core_crow_dominance=True,
            elliptic_backreaction_bound=False,
            reconnection_window_lower_bound=False,
            viscous_decay_window=False,
            nonlinear_deformation_control=False,
            positive_flux_accumulation=False,
            kstar_collapse_threshold=False,
            forbidden_dependencies=("numerical_only_evidence",),
            verdict="reject",
            concrete_rejection_reason=(
                "Numerical timing can suggest a reconnection episode, but "
                "numerical-only evidence does not establish the analytic lower "
                "bound, elliptic backreaction control, or collapse threshold."
            ),
        ),
        ReconnectionWindowCandidate(
            family_id="TKC",
            family="target_kstar_collapse_assumption",
            ansatz=(
                "assume target k-star collapse occurs after a forced reconnection "
                "duration and use it to certify the window"
            ),
            classification="forbidden target-collapse mechanism",
            thin_core_crow_dominance=False,
            elliptic_backreaction_bound=False,
            reconnection_window_lower_bound=False,
            viscous_decay_window=False,
            nonlinear_deformation_control=False,
            positive_flux_accumulation=True,
            kstar_collapse_threshold=True,
            forbidden_dependencies=(
                "assumed_blowup",
                "external_forcing",
                "target_kstar_collapse",
            ),
            verdict="reject",
            concrete_rejection_reason=(
                "The mechanism assumes blowup or target k-star collapse and relies "
                "on external forcing, so it cannot be accepted as an unforced "
                "reconnection-window source."
            ),
        ),
    ]


def build_summary() -> dict[str, Any]:
    rows = [candidate.row() for candidate in candidate_families()]
    accepted = [row for row in rows if row["accepted"]]
    partial = [row for row in rows if row["verdict"] == "partial"]
    return {
        "contract": CONTRACT,
        "complete": False,
        "proof_claimed": False,
        "scope": "deterministic classifier for reconnection-window lower-bound mechanisms under unforced NSE",
        "fail_closed": True,
        "route_decision": ROUTE_DECISION,
        "final_decision": ROUTE_DECISION,
        "accepted_source_count": len(accepted),
        "partial_source_count": len(partial),
        "candidate_family_count": len(rows),
        "required_gates": list(REQUIRED_GATES),
        "forbidden_dependencies": list(FORBIDDEN_DEPENDENCIES),
        "accepted_families": [row["family"] for row in accepted],
        "partial_families": [row["family"] for row in partial],
        "rejected_families": [row["family"] for row in rows if not row["accepted"]],
        "thin_core_rate_correction_partial": any(
            row["family"] == "thin_core_rate_correction"
            and row["verdict"] == "partial"
            for row in rows
        ),
        "elliptic_backreaction_partial": any(
            row["family"] == "elliptic_backreaction_bound"
            and row["verdict"] == "partial"
            for row in rows
        ),
        "reconnection_window_lower_bound_closed": any(
            row["reconnection_window_lower_bound"] and row["accepted"] for row in rows
        ),
        "clay_navier_stokes_promoted": False,
        "clay": False,
        "sprint114_reconnection_window_source_closed": False,
        "fail_closed_reason": (
            "No candidate simultaneously supplies thin-core Crow dominance, "
            "elliptic backreaction control, a reconnection-window lower bound, a "
            "viscous decay window, nonlinear deformation control, positive flux "
            "accumulation, a k-star collapse threshold, and absence of forbidden "
            "dependencies."
        ),
        "control_card": {
            "O": "classify possible sources for a reconnection-window lower bound under unforced NSE",
            "R": "all eight gates must pass and forbidden dependencies must be absent",
            "C": "single deterministic Python ledger emitting summary JSON, rows JSON, CSV, and Markdown",
            "S": "seven candidate families evaluated in fixed order",
            "L": "acceptance is the conjunction of gate_results; partial supporting evidence is never accepted",
            "P": ROUTE_DECISION,
            "G": "accepted_source_count is fixed at zero and Clay Navier-Stokes promotion remains false",
            "F": "thin-core rate correction and elliptic backreaction are partial/supporting only",
        },
        "rows": rows,
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 114 Reconnection-Window Classifier",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Fail closed: `{str(summary['fail_closed']).lower()}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Accepted source count: `{summary['accepted_source_count']}`",
        f"- Partial source count: `{summary['partial_source_count']}`",
        f"- Candidate family count: `{summary['candidate_family_count']}`",
        f"- Thin-core rate correction partial: `{str(summary['thin_core_rate_correction_partial']).lower()}`",
        f"- Elliptic backreaction partial: `{str(summary['elliptic_backreaction_partial']).lower()}`",
        f"- Reconnection-window lower bound closed: `{str(summary['reconnection_window_lower_bound_closed']).lower()}`",
        f"- Clay Navier-Stokes promoted: `{str(summary['clay_navier_stokes_promoted']).lower()}`",
        f"- Clay: `{str(summary['clay']).lower()}`",
        "- Required gates: " + ", ".join(f"`{gate}`" for gate in summary["required_gates"]),
        "- Forbidden dependencies: "
        + ", ".join(f"`{item}`" for item in summary["forbidden_dependencies"]),
        "",
        "| Family | Verdict | Accepted | Failed gates | Forbidden dependencies | Concrete rejection reason |",
        "| --- | --- | --- | --- | --- | --- |",
    ]
    for row in summary["rows"]:
        failed = "none" if not row["failed_gates"] else ", ".join(f"`{gate}`" for gate in row["failed_gates"])
        lines.append(
            f"| `{row['family']}` | `{row['verdict']}` | `{str(row['accepted']).lower()}` | "
            f"{failed} | `{row['forbidden_dependencies']}` | {row['concrete_rejection_reason']} |"
        )
    lines.extend(["", summary["fail_closed_reason"]])
    return "\n".join(lines) + "\n"


def write_csv(out_dir: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = [
        "family_id",
        "family",
        "ansatz",
        "classification",
        "thin_core_crow_dominance",
        "elliptic_backreaction_bound",
        "reconnection_window_lower_bound",
        "viscous_decay_window",
        "nonlinear_deformation_control",
        "positive_flux_accumulation",
        "kstar_collapse_threshold",
        "no_forbidden_dependency",
        "forbidden_dependencies",
        "failed_gates",
        "accepted",
        "verdict",
        "concrete_rejection_reason",
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
    print(
        json.dumps(
            {
                key: summary[key]
                for key in (
                    "contract",
                    "route_decision",
                    "accepted_source_count",
                    "partial_source_count",
                    "thin_core_rate_correction_partial",
                    "elliptic_backreaction_partial",
                    "reconnection_window_lower_bound_closed",
                    "clay",
                )
            },
            sort_keys=True,
        )
    )
    return 1 if summary["accepted_source_count"] == 0 else 0


if __name__ == "__main__":
    raise SystemExit(main())
