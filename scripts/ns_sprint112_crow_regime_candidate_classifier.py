#!/usr/bin/env python3
"""Sprint 112 NS thick-core Crow-regime candidate classifier."""

from __future__ import annotations

import argparse
import csv
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint112_crow_regime_candidate_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint112_crow_regime_candidate_classifier")
SUMMARY_NAME = "ns_sprint112_crow_regime_candidate_classifier_summary.json"
ROWS_NAME = "ns_sprint112_crow_regime_candidate_classifier_rows.json"
CSV_NAME = "ns_sprint112_crow_regime_candidate_classifier_rows.csv"
REPORT_NAME = "ns_sprint112_crow_regime_candidate_classifier.md"
ROUTE_DECISION = "FAIL_CLOSED_THICK_CORE_CROW_DOMINANCE_SOURCE"

REQUIRED_GATES = (
    "divergence_free_leray_data",
    "thick_core_ratio_delta_over_b_ge_half",
    "initial_crow_over_elliptic_rate_dominance",
    "compressive_eigenframe_alignment_source",
    "persistence_under_nse",
    "elliptic_backreaction_bound",
    "finite_time_flux_surplus",
    "no_forbidden_dependency",
)

FORBIDDEN_DEPENDENCIES = (
    "assumed_blowup",
    "desired_flux_sign",
    "imposed_alignment",
    "imposed_colocation",
    "numerical_only_evidence",
    "external_forcing",
    "non_leray_regularization",
    "target_kstar_collapse",
)


@dataclass(frozen=True)
class CrowRegimeCandidate:
    family_id: str
    family: str
    ansatz: str
    classification: str
    divergence_free_leray_data: bool
    thick_core_ratio_delta_over_b_ge_half: bool
    initial_crow_over_elliptic_rate_dominance: bool
    compressive_eigenframe_alignment_source: bool
    persistence_under_nse: bool
    elliptic_backreaction_bound: bool
    finite_time_flux_surplus: bool
    forbidden_dependencies: tuple[str, ...]
    verdict: str
    concrete_rejection_reason: str

    @property
    def no_forbidden_dependency(self) -> bool:
        return len(self.forbidden_dependencies) == 0

    @property
    def gate_results(self) -> dict[str, bool]:
        return {
            "divergence_free_leray_data": self.divergence_free_leray_data,
            "thick_core_ratio_delta_over_b_ge_half": self.thick_core_ratio_delta_over_b_ge_half,
            "initial_crow_over_elliptic_rate_dominance": self.initial_crow_over_elliptic_rate_dominance,
            "compressive_eigenframe_alignment_source": self.compressive_eigenframe_alignment_source,
            "persistence_under_nse": self.persistence_under_nse,
            "elliptic_backreaction_bound": self.elliptic_backreaction_bound,
            "finite_time_flux_surplus": self.finite_time_flux_surplus,
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


def candidate_families() -> list[CrowRegimeCandidate]:
    return [
        CrowRegimeCandidate(
            family_id="IRP",
            family="initial_rate_only_thick_core_vortex_pair",
            ansatz=(
                "choose smooth anti-parallel thick-core vortex-pair data with "
                "delta over b at least one half and compare only the initial Crow "
                "growth rate against the elliptic rate"
            ),
            classification=(
                "partial initial-rate witness for thick-core Crow dominance without "
                "NSE persistence or flux surplus closure"
            ),
            divergence_free_leray_data=True,
            thick_core_ratio_delta_over_b_ge_half=True,
            initial_crow_over_elliptic_rate_dominance=True,
            compressive_eigenframe_alignment_source=False,
            persistence_under_nse=False,
            elliptic_backreaction_bound=False,
            finite_time_flux_surplus=False,
            forbidden_dependencies=(),
            verdict="partial",
            concrete_rejection_reason=(
                "The thick-core pair can be Leray-compatible and supports an initial "
                "Crow-over-elliptic rate comparison, but it does not derive a "
                "compressive eigenframe alignment source, persistence under NSE, an "
                "elliptic backreaction bound, or finite-time flux surplus."
            ),
        ),
        CrowRegimeCandidate(
            family_id="TCV",
            family="thick_core_vortex_pair_with_prescribed_alignment",
            ansatz="place thick vortex cores so the Crow displacement, compression locus, and eigenframe are colocated",
            classification="geometric Crow setup with alignment supplied by construction",
            divergence_free_leray_data=True,
            thick_core_ratio_delta_over_b_ge_half=True,
            initial_crow_over_elliptic_rate_dominance=True,
            compressive_eigenframe_alignment_source=False,
            persistence_under_nse=False,
            elliptic_backreaction_bound=False,
            finite_time_flux_surplus=False,
            forbidden_dependencies=("imposed_alignment", "imposed_colocation"),
            verdict="reject",
            concrete_rejection_reason=(
                "The candidate selects the needed compression and eigenframe geometry "
                "by placement, so the alignment source is not derived and the "
                "NSE-persistent flux-surplus route remains open."
            ),
        ),
        CrowRegimeCandidate(
            family_id="NLW",
            family="non_leray_regularized_crow_wave_packet",
            ansatz="regularize a Crow-wave packet outside the Leray class to suppress elliptic deformation",
            classification="regularized packet model outside the admissible data class",
            divergence_free_leray_data=False,
            thick_core_ratio_delta_over_b_ge_half=True,
            initial_crow_over_elliptic_rate_dominance=True,
            compressive_eigenframe_alignment_source=True,
            persistence_under_nse=False,
            elliptic_backreaction_bound=True,
            finite_time_flux_surplus=False,
            forbidden_dependencies=("non_leray_regularization",),
            verdict="reject",
            concrete_rejection_reason=(
                "The regularization changes the admissible problem and does not give "
                "a Leray-data source or NSE persistence for the claimed flux surplus."
            ),
        ),
        CrowRegimeCandidate(
            family_id="NUM",
            family="numerical_thick_core_crow_episode",
            ansatz="promote simulated thick-core Crow episodes as the source of dominance",
            classification="computational observation without analytic persistence or flux proof",
            divergence_free_leray_data=True,
            thick_core_ratio_delta_over_b_ge_half=True,
            initial_crow_over_elliptic_rate_dominance=True,
            compressive_eigenframe_alignment_source=False,
            persistence_under_nse=False,
            elliptic_backreaction_bound=False,
            finite_time_flux_surplus=False,
            forbidden_dependencies=("numerical_only_evidence",),
            verdict="reject",
            concrete_rejection_reason=(
                "Numerical episodes may suggest a thick-core Crow window, but they do "
                "not supply analytic compressive alignment, persistence under NSE, "
                "elliptic backreaction control, or finite-time flux surplus."
            ),
        ),
        CrowRegimeCandidate(
            family_id="TKS",
            family="target_kstar_collapse_crow_ansatz",
            ansatz="assume the Crow regime collapses the target k-star shell with the desired flux sign",
            classification="forbidden insertion of the desired collapse and sign",
            divergence_free_leray_data=False,
            thick_core_ratio_delta_over_b_ge_half=True,
            initial_crow_over_elliptic_rate_dominance=True,
            compressive_eigenframe_alignment_source=False,
            persistence_under_nse=False,
            elliptic_backreaction_bound=False,
            finite_time_flux_surplus=True,
            forbidden_dependencies=("desired_flux_sign", "target_kstar_collapse"),
            verdict="reject",
            concrete_rejection_reason=(
                "The ansatz inserts the target shell collapse and flux sign directly, "
                "and therefore cannot be an independent thick-core Crow dominance "
                "source."
            ),
        ),
        CrowRegimeCandidate(
            family_id="FOR",
            family="externally_forced_crow_dominance_profile",
            ansatz="drive a thick-core Crow profile with forcing chosen to preserve the dominance interval",
            classification="forced mechanism outside unforced Navier-Stokes data classification",
            divergence_free_leray_data=False,
            thick_core_ratio_delta_over_b_ge_half=True,
            initial_crow_over_elliptic_rate_dominance=True,
            compressive_eigenframe_alignment_source=True,
            persistence_under_nse=True,
            elliptic_backreaction_bound=True,
            finite_time_flux_surplus=True,
            forbidden_dependencies=("external_forcing",),
            verdict="reject",
            concrete_rejection_reason=(
                "The dominance interval is maintained by external forcing, so the "
                "candidate is not an unforced Leray-data mechanism for Clay-relevant "
                "Navier-Stokes closure."
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
        "scope": "deterministic classifier for thick-core Crow dominance candidate data mechanisms",
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
        "clay_navier_stokes_promoted": False,
        "clay": False,
        "sprint112_thick_core_crow_dominance_source_closed": False,
        "fail_closed_reason": (
            "No candidate simultaneously derives Leray data, thick-core ratio "
            "delta over b at least one half, initial Crow-over-elliptic rate "
            "dominance, a compressive eigenframe alignment source, persistence "
            "under NSE, an elliptic backreaction bound, finite-time flux surplus, "
            "and absence of forbidden dependencies."
        ),
        "control_card": {
            "O": "classify thick-core Crow dominance candidate data mechanisms",
            "R": "all eight gates must pass and forbidden dependencies must be absent",
            "C": "single deterministic Python ledger emitting summary JSON, rows JSON, CSV, and Markdown",
            "S": "six candidate families evaluated in fixed order",
            "L": "acceptance is the conjunction of gate_results; partial is never accepted",
            "P": ROUTE_DECISION,
            "G": "accepted_source_count is fixed at zero and Clay Navier-Stokes promotion remains false",
            "F": "initial-rate-only thick-core pair reaches partial status but fails persistence and flux gates",
        },
        "rows": rows,
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 112 Thick-Core Crow-Regime Candidate Classifier",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Fail closed: `{str(summary['fail_closed']).lower()}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Accepted source count: `{summary['accepted_source_count']}`",
        f"- Partial source count: `{summary['partial_source_count']}`",
        f"- Candidate family count: `{summary['candidate_family_count']}`",
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
        "divergence_free_leray_data",
        "thick_core_ratio_delta_over_b_ge_half",
        "initial_crow_over_elliptic_rate_dominance",
        "compressive_eigenframe_alignment_source",
        "persistence_under_nse",
        "elliptic_backreaction_bound",
        "finite_time_flux_surplus",
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
                    "clay",
                )
            },
            sort_keys=True,
        )
    )
    return 1 if summary["accepted_source_count"] == 0 else 0


if __name__ == "__main__":
    raise SystemExit(main())
