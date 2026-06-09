#!/usr/bin/env python3
"""Sprint 103 NS compression-locus geometry classifier."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint103_compression_locus_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint103_compression_locus_classifier")
SUMMARY_NAME = "ns_sprint103_compression_locus_classifier_summary.json"
ROWS_NAME = "ns_sprint103_compression_locus_classifier_rows.json"
REPORT_NAME = "ns_sprint103_compression_locus_classifier.md"
ROUTE_DECISION = "FAIL_CLOSED_COMPRESSION_LOCUS_GEOMETRY"

REQUIRED_GATES = (
    "concentration_measure",
    "compressive_strain_locus",
    "eigenframe_alignment",
    "colocation_estimate",
    "leray_compatible",
    "non_circular_source",
    "no_forbidden_dependency",
)

FORBIDDEN_DEPENDENCIES = (
    "assumed_bkm_failure",
    "assumed_serrin_failure",
    "assumed_singularity",
    "target_blowup",
    "desired_conclusion",
    "external_forcing",
    "imposed_compression_sign",
    "imposed_compression_locus",
    "imposed_concentration_locus",
    "imposed_colocation",
    "imposed_compressive_locus",
    "imposed_eigenframe_alignment",
    "target_kstar_collapse",
)


@dataclass(frozen=True)
class CompressionLocusCandidate:
    family_id: str
    family: str
    ansatz: str
    classification: str
    concentration_measure: bool
    compressive_strain_locus: bool
    eigenframe_alignment: bool
    colocation_estimate: bool
    leray_compatible: bool
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
            "concentration_measure": self.concentration_measure,
            "compressive_strain_locus": self.compressive_strain_locus,
            "eigenframe_alignment": self.eigenframe_alignment,
            "colocation_estimate": self.colocation_estimate,
            "leray_compatible": self.leray_compatible,
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


def candidate_families() -> list[CompressionLocusCandidate]:
    return [
        CompressionLocusCandidate(
            family_id="M1",
            family="measured_concentration_locus",
            ansatz="derive a high-frequency concentration measure from shell energy",
            classification="measure extraction without sign geometry",
            concentration_measure=True,
            compressive_strain_locus=False,
            eigenframe_alignment=False,
            colocation_estimate=False,
            leray_compatible=True,
            non_circular_source=False,
            forbidden_dependencies=(),
            verdict="reject",
            note="A concentration measure does not locate compressive low-mode strain or align the high-frequency energy tensor with that strain.",
        ),
        CompressionLocusCandidate(
            family_id="E1",
            family="low_strain_eigenvalue_barrier",
            ansatz="use negative low-strain eigenvalues as a compression barrier",
            classification="strain-sign locus without high-frequency colocation",
            concentration_measure=False,
            compressive_strain_locus=True,
            eigenframe_alignment=False,
            colocation_estimate=False,
            leray_compatible=True,
            non_circular_source=False,
            forbidden_dependencies=(),
            verdict="reject",
            note="A compressive strain region alone does not show high-frequency energy concentrates there or in the compressive eigendirections.",
        ),
        CompressionLocusCandidate(
            family_id="A1",
            family="eigenframe_alignment_transport",
            ansatz="transport high-frequency eigenframes into compressive low-strain directions",
            classification="alignment transport without closed colocation",
            concentration_measure=True,
            compressive_strain_locus=True,
            eigenframe_alignment=False,
            colocation_estimate=False,
            leray_compatible=True,
            non_circular_source=False,
            forbidden_dependencies=("imposed_eigenframe_alignment",),
            verdict="reject",
            note="The needed eigenframe alignment is imposed at the step where it must be derived from unforced dynamics.",
        ),
        CompressionLocusCandidate(
            family_id="V1",
            family="vortex_tube_self_alignment",
            ansatz="vortex tubes self-align high-frequency energy with compressive strain",
            classification="vortex-geometry narrative",
            concentration_measure=False,
            compressive_strain_locus=True,
            eigenframe_alignment=False,
            colocation_estimate=False,
            leray_compatible=True,
            non_circular_source=False,
            forbidden_dependencies=("desired_conclusion",),
            verdict="reject",
            note="Vortex-tube geometry is compatible with the intended picture, but the self-alignment mechanism is not derived without the desired collapse geometry.",
        ),
        CompressionLocusCandidate(
            family_id="I1",
            family="imposed_colocation",
            ansatz="select the high-frequency locus to coincide with compressive strain",
            classification="forbidden imposed colocation",
            concentration_measure=True,
            compressive_strain_locus=True,
            eigenframe_alignment=True,
            colocation_estimate=True,
            leray_compatible=False,
            non_circular_source=False,
            forbidden_dependencies=("imposed_colocation", "imposed_compressive_locus", "desired_conclusion"),
            verdict="reject",
            note="This builds the required colocation into the candidate and is therefore circular for the unforced Leray route.",
        ),
    ]


def build_summary() -> dict[str, Any]:
    rows = [candidate.row() for candidate in candidate_families()]
    accepted = [row for row in rows if row["accepted"]]
    return {
        "contract": CONTRACT,
        "complete": False,
        "proof_claimed": False,
        "scope": "deterministic classifier for compression-locus geometry mechanisms",
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
        "sprint103_compression_locus_geometry_closed": False,
        "fail_closed_reason": (
            "No candidate derives concentration, compressive strain, eigenframe alignment, "
            "and colocation from a non-circular Leray-compatible source."
        ),
        "control_card": {
            "O": "classify candidate compression-locus geometry sources",
            "R": "all seven gates must pass and forbidden dependencies must be absent",
            "C": "single deterministic Python ledger emitting JSON and Markdown",
            "S": "five candidates evaluated in fixed order",
            "L": "acceptance is conjunction of gate_results",
            "P": ROUTE_DECISION,
            "G": "Clay Navier-Stokes promotion remains false",
            "F": "all candidates fail the non_circular_source gate",
        },
        "rows": rows,
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 103 Compression-Locus Geometry Classifier",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Fail closed: `{str(summary['fail_closed']).lower()}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Accepted source count: `{summary['accepted_source_count']}`",
        f"- Candidate family count: `{summary['candidate_family_count']}`",
        f"- Clay Navier-Stokes promoted: `{str(summary['clay_navier_stokes_promoted']).lower()}`",
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
    write_outputs(args.out_dir, summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
