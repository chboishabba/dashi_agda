#!/usr/bin/env python3
"""Sprint 111 NS strain-compression candidate classifier."""

from __future__ import annotations

import argparse
import csv
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint111_strain_compression_candidate_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint111_strain_compression_candidate_classifier")
SUMMARY_NAME = "ns_sprint111_strain_compression_candidate_classifier_summary.json"
ROWS_NAME = "ns_sprint111_strain_compression_candidate_classifier_rows.json"
CSV_NAME = "ns_sprint111_strain_compression_candidate_classifier_rows.csv"
REPORT_NAME = "ns_sprint111_strain_compression_candidate_classifier.md"
ROUTE_DECISION = "FAIL_CLOSED_STRAIN_COMPRESSION_CORRELATION_SOURCE"

REQUIRED_GATES = (
    "divergence_free_leray_compatible_data",
    "compressive_low_mode_strain_locus",
    "high_frequency_energy_concentration",
    "eigenframe_alignment",
    "persistent_positive_strain_contraction",
    "non_circular_source",
    "no_forbidden_dependency",
)

FORBIDDEN_DEPENDENCIES = (
    "assumed_blowup",
    "assumed_bkm_failure",
    "assumed_serrin_failure",
    "target_kstar_collapse",
    "desired_flux_sign",
    "imposed_compressive_colocation",
    "imposed_eigenframe_alignment",
    "numerical_only_evidence",
    "external_forcing",
    "non_leray_regularization",
)


@dataclass(frozen=True)
class StrainCompressionCandidate:
    family_id: str
    family: str
    ansatz: str
    classification: str
    divergence_free_leray_compatible_data: bool
    compressive_low_mode_strain_locus: bool
    high_frequency_energy_concentration: bool
    eigenframe_alignment: bool
    persistent_positive_strain_contraction: bool
    non_circular_source: bool
    forbidden_dependencies: tuple[str, ...]
    verdict: str
    concrete_rejection_reason: str

    @property
    def no_forbidden_dependency(self) -> bool:
        return len(self.forbidden_dependencies) == 0

    @property
    def gate_results(self) -> dict[str, bool]:
        return {
            "divergence_free_leray_compatible_data": self.divergence_free_leray_compatible_data,
            "compressive_low_mode_strain_locus": self.compressive_low_mode_strain_locus,
            "high_frequency_energy_concentration": self.high_frequency_energy_concentration,
            "eigenframe_alignment": self.eigenframe_alignment,
            "persistent_positive_strain_contraction": self.persistent_positive_strain_contraction,
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


def candidate_families() -> list[StrainCompressionCandidate]:
    return [
        StrainCompressionCandidate(
            family_id="AVR",
            family="axisymmetric_vortex_ring_data",
            ansatz="use smooth axisymmetric vortex-ring data as the strain-compression source",
            classification="Leray-compatible symmetric data without a durable high-frequency contraction mechanism",
            divergence_free_leray_compatible_data=True,
            compressive_low_mode_strain_locus=True,
            high_frequency_energy_concentration=False,
            eigenframe_alignment=False,
            persistent_positive_strain_contraction=False,
            non_circular_source=False,
            forbidden_dependencies=(),
            verdict="reject",
            concrete_rejection_reason=(
                "The data can be divergence-free and unforced, but symmetry alone does "
                "not derive high-frequency energy concentration, eigenframe alignment, "
                "or persistent positive strain contraction from a non-circular source."
            ),
        ),
        StrainCompressionCandidate(
            family_id="APV",
            family="anti_parallel_vortex_tube_pair",
            ansatz="place anti-parallel vortex tubes so the interaction region compresses high modes",
            classification="geometric tube interaction with colocation supplied by arrangement",
            divergence_free_leray_compatible_data=True,
            compressive_low_mode_strain_locus=True,
            high_frequency_energy_concentration=False,
            eigenframe_alignment=False,
            persistent_positive_strain_contraction=False,
            non_circular_source=False,
            forbidden_dependencies=("imposed_compressive_colocation",),
            verdict="reject",
            concrete_rejection_reason=(
                "The pair identifies a compressive interaction region only by arranging "
                "the tubes there; it does not close high-frequency concentration or "
                "persistent contraction without imposed colocation."
            ),
        ),
        StrainCompressionCandidate(
            family_id="SSP",
            family="strained_shear_layer_packet",
            ansatz="evolve a localized shear layer packet through a low-mode strain field",
            classification="packet model with strain geometry but no closed contraction sign",
            divergence_free_leray_compatible_data=True,
            compressive_low_mode_strain_locus=True,
            high_frequency_energy_concentration=True,
            eigenframe_alignment=False,
            persistent_positive_strain_contraction=False,
            non_circular_source=False,
            forbidden_dependencies=("desired_flux_sign",),
            verdict="reject",
            concrete_rejection_reason=(
                "The packet can localize energy near a compressive low-mode locus, but "
                "the eigenframe alignment and positive contraction sign are selected "
                "toward the desired flux behavior rather than derived."
            ),
        ),
        StrainCompressionCandidate(
            family_id="NOV",
            family="numerically_observed_vortex_stretching",
            ansatz="promote numerical vortex-stretching episodes as evidence for the source",
            classification="computational observation without analytic non-circular closure",
            divergence_free_leray_compatible_data=True,
            compressive_low_mode_strain_locus=True,
            high_frequency_energy_concentration=True,
            eigenframe_alignment=True,
            persistent_positive_strain_contraction=False,
            non_circular_source=False,
            forbidden_dependencies=("numerical_only_evidence",),
            verdict="reject",
            concrete_rejection_reason=(
                "The observed episodes may show transient alignment, but numerical-only "
                "evidence does not prove persistent positive strain contraction in the "
                "Leray class and cannot serve as the non-circular Clay source."
            ),
        ),
        StrainCompressionCandidate(
            family_id="ICA",
            family="imposed_colocation_ansatz",
            ansatz="assume concentration, compressive strain, and eigenframe alignment occur together",
            classification="forbidden direct insertion of the target correlation",
            divergence_free_leray_compatible_data=False,
            compressive_low_mode_strain_locus=True,
            high_frequency_energy_concentration=True,
            eigenframe_alignment=True,
            persistent_positive_strain_contraction=True,
            non_circular_source=False,
            forbidden_dependencies=(
                "imposed_compressive_colocation",
                "imposed_eigenframe_alignment",
                "target_kstar_collapse",
            ),
            verdict="reject",
            concrete_rejection_reason=(
                "The target correlation is built into the ansatz, and the construction "
                "does not supply independent divergence-free Leray-compatible data or "
                "a non-circular source."
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
        "scope": "deterministic classifier for Clay-relevant strain-compression candidate mechanisms",
        "fail_closed": True,
        "route_decision": ROUTE_DECISION,
        "final_decision": ROUTE_DECISION,
        "accepted_source_count": len(accepted),
        "candidate_family_count": len(rows),
        "required_gates": list(REQUIRED_GATES),
        "forbidden_dependencies": list(FORBIDDEN_DEPENDENCIES),
        "accepted_families": [row["family"] for row in accepted],
        "rejected_families": [row["family"] for row in rows if not row["accepted"]],
        "clay_navier_stokes_promoted": False,
        "clay": False,
        "sprint111_strain_compression_correlation_source_closed": False,
        "fail_closed_reason": (
            "No candidate simultaneously derives Leray-compatible data, a compressive "
            "low-mode strain locus, high-frequency concentration, eigenframe alignment, "
            "persistent positive strain contraction, and a non-circular source while "
            "avoiding forbidden dependencies."
        ),
        "control_card": {
            "O": "classify Clay-relevant strain-compression candidate mechanisms",
            "R": "all seven gates must pass and forbidden dependencies must be absent",
            "C": "single deterministic Python ledger emitting summary JSON, rows JSON, CSV, and Markdown",
            "S": "five requested candidates evaluated in fixed order",
            "L": "acceptance is the conjunction of gate_results",
            "P": ROUTE_DECISION,
            "G": "accepted_source_count is fixed at zero and Clay Navier-Stokes promotion remains false",
            "F": "every candidate fails non_circular_source or a required analytic correlation gate",
        },
        "rows": rows,
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 111 Strain-Compression Candidate Classifier",
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
        "| Family | Accepted | Failed gates | Forbidden dependencies | Concrete rejection reason |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in summary["rows"]:
        failed = "none" if not row["failed_gates"] else ", ".join(f"`{gate}`" for gate in row["failed_gates"])
        lines.append(
            f"| `{row['family']}` | `{str(row['accepted']).lower()}` | {failed} | "
            f"`{row['forbidden_dependencies']}` | {row['concrete_rejection_reason']} |"
        )
    lines.extend(["", summary["fail_closed_reason"]])
    return "\n".join(lines) + "\n"


def write_csv(out_dir: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = [
        "family_id",
        "family",
        "ansatz",
        "classification",
        "divergence_free_leray_compatible_data",
        "compressive_low_mode_strain_locus",
        "high_frequency_energy_concentration",
        "eigenframe_alignment",
        "persistent_positive_strain_contraction",
        "non_circular_source",
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
                for key in ("contract", "route_decision", "accepted_source_count", "clay")
            },
            sort_keys=True,
        )
    )
    return 1 if summary["fail_closed"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
