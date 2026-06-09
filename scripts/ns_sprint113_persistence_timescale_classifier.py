#!/usr/bin/env python3
"""Sprint 113 NS Crow-persistence timescale mechanism classifier."""

from __future__ import annotations

import argparse
import csv
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint113_persistence_timescale_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint113_persistence_timescale_classifier")
SUMMARY_NAME = "ns_sprint113_persistence_timescale_classifier_summary.json"
ROWS_NAME = "ns_sprint113_persistence_timescale_classifier_rows.json"
CSV_NAME = "ns_sprint113_persistence_timescale_classifier_rows.csv"
REPORT_NAME = "ns_sprint113_persistence_timescale_classifier.md"
ROUTE_DECISION = "FAIL_CLOSED_CROW_PERSISTENCE_TIMESCALE_SOURCE"

REQUIRED_GATES = (
    "leray_compatible_initial_data",
    "initial_crow_dominance_imported",
    "nonlinear_deformation_control",
    "viscous_decay_window",
    "elliptic_mode_leakage_control",
    "persistence_timescale_lower_bound",
    "positive_flux_accumulation_window",
    "no_forbidden_dependency",
)

FORBIDDEN_DEPENDENCIES = (
    "assumed_blowup",
    "desired_flux_surplus",
    "imposed_persistence",
    "imposed_alignment",
    "external_forcing",
    "numerical_only_evidence",
    "target_kstar_collapse",
    "hidden_smooth_continuation",
)


@dataclass(frozen=True)
class PersistenceTimescaleCandidate:
    family_id: str
    family: str
    ansatz: str
    classification: str
    leray_compatible_initial_data: bool
    initial_crow_dominance_imported: bool
    nonlinear_deformation_control: bool
    viscous_decay_window: bool
    elliptic_mode_leakage_control: bool
    persistence_timescale_lower_bound: bool
    positive_flux_accumulation_window: bool
    forbidden_dependencies: tuple[str, ...]
    verdict: str
    concrete_rejection_reason: str

    @property
    def no_forbidden_dependency(self) -> bool:
        return len(self.forbidden_dependencies) == 0

    @property
    def gate_results(self) -> dict[str, bool]:
        return {
            "leray_compatible_initial_data": self.leray_compatible_initial_data,
            "initial_crow_dominance_imported": self.initial_crow_dominance_imported,
            "nonlinear_deformation_control": self.nonlinear_deformation_control,
            "viscous_decay_window": self.viscous_decay_window,
            "elliptic_mode_leakage_control": self.elliptic_mode_leakage_control,
            "persistence_timescale_lower_bound": self.persistence_timescale_lower_bound,
            "positive_flux_accumulation_window": self.positive_flux_accumulation_window,
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


def candidate_families() -> list[PersistenceTimescaleCandidate]:
    return [
        PersistenceTimescaleCandidate(
            family_id="IRC",
            family="imported_thick_core_initial_rate",
            ansatz=(
                "import the Sprint 112 thick-core initial Crow-over-elliptic rate "
                "comparison and ask whether it persists under unforced NSE"
            ),
            classification=(
                "partial initial-rate source; imports dominance at t=0 but does not "
                "derive a persistence timescale"
            ),
            leray_compatible_initial_data=True,
            initial_crow_dominance_imported=True,
            nonlinear_deformation_control=False,
            viscous_decay_window=False,
            elliptic_mode_leakage_control=False,
            persistence_timescale_lower_bound=False,
            positive_flux_accumulation_window=False,
            forbidden_dependencies=(),
            verdict="partial",
            concrete_rejection_reason=(
                "The imported thick-core initial-rate comparison is admissible as an "
                "initial witness, but it does not control nonlinear deformation, "
                "viscous decay, elliptic leakage, or a positive-flux accumulation "
                "window over a derived NSE timescale."
            ),
        ),
        PersistenceTimescaleCandidate(
            family_id="LCO",
            family="linearized_crow_eigenmode_only",
            ansatz=(
                "evolve only the linearized Crow eigenmode and treat its growth "
                "interval as the nonlinear persistence interval"
            ),
            classification="linear spectral proxy without nonlinear NSE persistence closure",
            leray_compatible_initial_data=True,
            initial_crow_dominance_imported=True,
            nonlinear_deformation_control=False,
            viscous_decay_window=True,
            elliptic_mode_leakage_control=False,
            persistence_timescale_lower_bound=False,
            positive_flux_accumulation_window=False,
            forbidden_dependencies=("imposed_persistence",),
            verdict="reject",
            concrete_rejection_reason=(
                "The linearized eigenmode can encode an initial Crow direction and a "
                "formal viscous damping scale, but nonlinear deformation and elliptic "
                "mode leakage are not controlled; persistence is inserted by the "
                "linear model rather than derived for unforced NSE."
            ),
        ),
        PersistenceTimescaleCandidate(
            family_id="PST",
            family="perturbative_short_time_smooth_solution",
            ansatz=(
                "use local smooth well-posedness around smooth thick-core data to "
                "propagate the initial Crow inequality for a short time"
            ),
            classification="short-time perturbative continuation without flux-window closure",
            leray_compatible_initial_data=True,
            initial_crow_dominance_imported=True,
            nonlinear_deformation_control=True,
            viscous_decay_window=False,
            elliptic_mode_leakage_control=False,
            persistence_timescale_lower_bound=False,
            positive_flux_accumulation_window=False,
            forbidden_dependencies=("hidden_smooth_continuation",),
            verdict="reject",
            concrete_rejection_reason=(
                "Local smooth continuation can bound deformation only while the "
                "smooth solution is already available, and it supplies neither an "
                "explicit viscous decay window nor elliptic leakage control strong "
                "enough to force positive flux accumulation."
            ),
        ),
        PersistenceTimescaleCandidate(
            family_id="ELL",
            family="energy_class_leray_only",
            ansatz="use the global Leray energy inequality alone as the persistence source",
            classification="energy-class existence without mode-resolved Crow persistence",
            leray_compatible_initial_data=True,
            initial_crow_dominance_imported=False,
            nonlinear_deformation_control=False,
            viscous_decay_window=True,
            elliptic_mode_leakage_control=False,
            persistence_timescale_lower_bound=False,
            positive_flux_accumulation_window=False,
            forbidden_dependencies=(),
            verdict="reject",
            concrete_rejection_reason=(
                "The Leray energy class is admissible and dissipative, but the energy "
                "inequality alone does not import Crow dominance, resolve elliptic "
                "mode leakage, or give a lower bound for a positive-flux Crow window."
            ),
        ),
        PersistenceTimescaleCandidate(
            family_id="EFP",
            family="externally_forced_persistence",
            ansatz="add forcing chosen to keep the Crow displacement dominant over elliptic leakage",
            classification="forced persistence mechanism outside the unforced NSE classification",
            leray_compatible_initial_data=False,
            initial_crow_dominance_imported=True,
            nonlinear_deformation_control=True,
            viscous_decay_window=True,
            elliptic_mode_leakage_control=True,
            persistence_timescale_lower_bound=True,
            positive_flux_accumulation_window=True,
            forbidden_dependencies=("external_forcing", "imposed_persistence"),
            verdict="reject",
            concrete_rejection_reason=(
                "The timescale is maintained by an external driver and imposed "
                "persistence, so the mechanism is not an unforced Leray-data source "
                "for Crow persistence."
            ),
        ),
        PersistenceTimescaleCandidate(
            family_id="NCE",
            family="numerical_crow_episode",
            ansatz="promote simulated Crow episodes as evidence for persistence and flux accumulation",
            classification="computational episode without analytic lower-bound proof",
            leray_compatible_initial_data=True,
            initial_crow_dominance_imported=True,
            nonlinear_deformation_control=False,
            viscous_decay_window=False,
            elliptic_mode_leakage_control=False,
            persistence_timescale_lower_bound=False,
            positive_flux_accumulation_window=False,
            forbidden_dependencies=("numerical_only_evidence",),
            verdict="reject",
            concrete_rejection_reason=(
                "The simulated episode may display transient Crow geometry, but "
                "numerical-only evidence does not derive nonlinear deformation "
                "control, leakage bounds, or a rigorous persistence timescale lower "
                "bound for unforced NSE."
            ),
        ),
        PersistenceTimescaleCandidate(
            family_id="TFS",
            family="target_flux_surplus_collapse",
            ansatz=(
                "assume the target k-star collapse persists until a desired positive "
                "flux surplus has accumulated"
            ),
            classification="forbidden insertion of the desired flux conclusion",
            leray_compatible_initial_data=False,
            initial_crow_dominance_imported=True,
            nonlinear_deformation_control=False,
            viscous_decay_window=False,
            elliptic_mode_leakage_control=False,
            persistence_timescale_lower_bound=True,
            positive_flux_accumulation_window=True,
            forbidden_dependencies=(
                "desired_flux_surplus",
                "imposed_persistence",
                "target_kstar_collapse",
            ),
            verdict="reject",
            concrete_rejection_reason=(
                "The candidate assumes the target collapse and desired flux surplus "
                "instead of deriving them from unforced NSE persistence estimates."
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
        "scope": "deterministic classifier for Crow persistence mechanisms under unforced NSE",
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
        "initial_rate_candidate_partial": any(
            row["family"] == "imported_thick_core_initial_rate"
            and row["verdict"] == "partial"
            for row in rows
        ),
        "clay_navier_stokes_promoted": False,
        "clay": False,
        "sprint113_persistence_timescale_source_closed": False,
        "fail_closed_reason": (
            "No candidate simultaneously supplies Leray-compatible initial data, "
            "imported initial Crow dominance, nonlinear deformation control, a "
            "viscous decay window, elliptic mode leakage control, a persistence "
            "timescale lower bound, positive flux accumulation, and absence of "
            "forbidden dependencies."
        ),
        "control_card": {
            "O": "classify possible mechanisms for Crow persistence under unforced NSE",
            "R": "all eight gates must pass and forbidden dependencies must be absent",
            "C": "single deterministic Python ledger emitting summary JSON, rows JSON, CSV, and Markdown",
            "S": "seven candidate families evaluated in fixed order",
            "L": "acceptance is the conjunction of gate_results; partial is never accepted",
            "P": ROUTE_DECISION,
            "G": "accepted_source_count is fixed at zero and Clay Navier-Stokes promotion remains false",
            "F": "imported thick-core initial rate is partial but fails every persistence-timescale gate",
        },
        "rows": rows,
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 113 Crow-Persistence Timescale Classifier",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Fail closed: `{str(summary['fail_closed']).lower()}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Accepted source count: `{summary['accepted_source_count']}`",
        f"- Partial source count: `{summary['partial_source_count']}`",
        f"- Candidate family count: `{summary['candidate_family_count']}`",
        f"- Initial-rate candidate partial: `{str(summary['initial_rate_candidate_partial']).lower()}`",
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
        "leray_compatible_initial_data",
        "initial_crow_dominance_imported",
        "nonlinear_deformation_control",
        "viscous_decay_window",
        "elliptic_mode_leakage_control",
        "persistence_timescale_lower_bound",
        "positive_flux_accumulation_window",
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
                    "initial_rate_candidate_partial",
                    "clay",
                )
            },
            sort_keys=True,
        )
    )
    return 1 if summary["accepted_source_count"] == 0 else 0


if __name__ == "__main__":
    raise SystemExit(main())
