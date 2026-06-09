#!/usr/bin/env python3
"""Sprint 102 NS strain-geometry sign source classifier.

This deterministic fail-closed ledger classifies candidate geometric
mechanisms for a signed compression source. A candidate is accepted only when
every required gate is supplied, including a non-circular compression gate, and
no forbidden dependency is present.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint102_strain_geometry_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint102_strain_geometry_classifier")
SUMMARY_NAME = "ns_sprint102_strain_geometry_classifier_summary.json"
ROWS_NAME = "ns_sprint102_strain_geometry_classifier_rows.json"
REPORT_NAME = "ns_sprint102_strain_geometry_classifier.md"
ROUTE_DECISION = "FAIL_CLOSED_STRAIN_GEOMETRY_SOURCE"

REQUIRED_GATES = (
    "ll_lh_vanish",
    "hh_strain_identity",
    "concentration_locus_correlation",
    "leray_compatible",
    "non_circular_compression_gate",
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
    "imposed_vortex_geometry",
    "imposed_pressure_alignment",
    "target_kstar_collapse",
    "imposed_concentration_locus",
)


@dataclass(frozen=True)
class StrainGeometrySource:
    family_id: str
    family: str
    ansatz: str
    classification: str
    ll_lh_vanish: bool
    hh_strain_identity: bool
    concentration_locus_correlation: bool
    leray_compatible: bool
    non_circular_compression_gate: bool
    forbidden_dependencies: tuple[str, ...]
    verdict: str
    note: str

    @property
    def no_forbidden_dependency(self) -> bool:
        return len(self.forbidden_dependencies) == 0

    @property
    def gate_results(self) -> dict[str, bool]:
        return {
            "ll_lh_vanish": self.ll_lh_vanish,
            "hh_strain_identity": self.hh_strain_identity,
            "concentration_locus_correlation": self.concentration_locus_correlation,
            "leray_compatible": self.leray_compatible,
            "non_circular_compression_gate": self.non_circular_compression_gate,
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


def candidate_families() -> list[StrainGeometrySource]:
    return [
        StrainGeometrySource(
            family_id="V1",
            family="vortex_core_compression",
            ansatz="localized vortex cores generate a favorable strain-compression sign",
            classification="geometric vortex-core compression narrative",
            ll_lh_vanish=False,
            hh_strain_identity=True,
            concentration_locus_correlation=False,
            leray_compatible=True,
            non_circular_compression_gate=False,
            forbidden_dependencies=("imposed_vortex_geometry", "imposed_compression_sign"),
            verdict="reject",
            note=(
                "A vortex-core picture is geometrically suggestive, but the favorable "
                "compression orientation is selected rather than derived from the Leray "
                "solution. Low/low and low/high leakage is not eliminated, and the core "
                "locus is not correlated to concentration by an independent estimate."
            ),
        ),
        StrainGeometrySource(
            family_id="S1",
            family="strain_energy_density_alignment",
            ansatz="high strain energy density aligns eigenvectors to force signed compression",
            classification="strain-eigenframe alignment heuristic",
            ll_lh_vanish=False,
            hh_strain_identity=True,
            concentration_locus_correlation=False,
            leray_compatible=True,
            non_circular_compression_gate=False,
            forbidden_dependencies=("desired_conclusion",),
            verdict="reject",
            note=(
                "The high/high strain identity is compatible with the energy ledger, but "
                "large strain density alone does not determine eigenframe sign after "
                "projection. The alignment needed for compression is the conclusion to be "
                "proved."
            ),
        ),
        StrainGeometrySource(
            family_id="L1",
            family="spectral_localization_geometry",
            ansatz="localizing the active shell fixes the spatial geometry of compression",
            classification="frequency-local geometric localization",
            ll_lh_vanish=False,
            hh_strain_identity=True,
            concentration_locus_correlation=False,
            leray_compatible=True,
            non_circular_compression_gate=False,
            forbidden_dependencies=("target_kstar_collapse",),
            verdict="reject",
            note=(
                "Spectral localization can isolate high/high terms in an identity, but it "
                "does not by itself force where physical concentration occurs or determine "
                "the sign of compression on that locus."
            ),
        ),
        StrainGeometrySource(
            family_id="P1",
            family="pressure_mediated_alignment",
            ansatz="pressure coupling aligns strain and vorticity to produce compression",
            classification="pressure-alignment sign assertion",
            ll_lh_vanish=False,
            hh_strain_identity=False,
            concentration_locus_correlation=False,
            leray_compatible=True,
            non_circular_compression_gate=False,
            forbidden_dependencies=("imposed_pressure_alignment",),
            verdict="reject",
            note=(
                "Pressure is part of the Leray projection, but it is not a free signed "
                "geometric source. The candidate does not close the high/high strain "
                "identity or remove lower interaction leakage without imposing alignment."
            ),
        ),
        StrainGeometrySource(
            family_id="I1",
            family="imposed_compression_locus",
            ansatz="choose a locus where high-frequency strain compression has the needed sign",
            classification="forbidden imposed compression source",
            ll_lh_vanish=True,
            hh_strain_identity=True,
            concentration_locus_correlation=True,
            leray_compatible=False,
            non_circular_compression_gate=False,
            forbidden_dependencies=(
                "imposed_concentration_locus",
                "imposed_compression_sign",
                "desired_conclusion",
            ),
            verdict="reject",
            note=(
                "The candidate builds the needed locus and sign into the construction, so "
                "it is circular and not compatible with an unforced Leray solution route."
            ),
        ),
    ]


def build_summary() -> dict[str, Any]:
    rows = [family.row() for family in candidate_families()]
    accepted = [
        row
        for row in rows
        if row["accepted"] and row["gate_results"]["non_circular_compression_gate"]
    ]
    fail_closed = not accepted
    accepted_source_count = len(accepted)
    return {
        "contract": CONTRACT,
        "complete": False,
        "proof_claimed": False,
        "scope": "deterministic classifier for candidate geometric signed compression mechanisms",
        "fail_closed": fail_closed,
        "route_decision": ROUTE_DECISION,
        "final_decision": ROUTE_DECISION,
        "accepted_source_count": accepted_source_count,
        "candidate_family_count": len(rows),
        "required_gates": list(REQUIRED_GATES),
        "forbidden_dependencies": list(FORBIDDEN_DEPENDENCIES),
        "accepted_families": [row["family"] for row in accepted],
        "rejected_families": [row["family"] for row in rows if not row["accepted"]],
        "option_b_closed": False,
        "clay_navier_stokes_promoted": False,
        "sprint102_strain_geometry_source_closed": False,
        "fail_closed_reason": (
            "No candidate family supplies a non-circular geometric compression source "
            "with LL/LH vanish, HH strain identity, concentration-locus correlation, "
            "Leray compatibility, and forbidden-dependency gates all closed."
        ),
        "computed_fail_closed_from_rows": fail_closed,
        "control_card": {
            "O": "classify candidate geometric sign sources for strain-driven compression",
            "R": "all six gates must pass, including a non-circular compression gate",
            "C": "single deterministic Python ledger emitting JSON and Markdown",
            "S": "five named candidate families evaluated in fixed order",
            "L": "acceptance is the conjunction of gate_results plus the non-circular compression gate",
            "P": ROUTE_DECISION,
            "G": "Option B remains open; Clay Navier-Stokes is not promoted",
            "F": "all candidates are rejected with concrete failed gates or dependencies",
        },
        "rows": rows,
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 102 Strain Geometry Classifier",
        "",
        f"- Contract: `{summary['contract']}`",
        "- Scope: deterministic geometric signed compression source classification.",
        "- Proof claimed: `false`",
        f"- Fail closed: `{str(summary['fail_closed']).lower()}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Accepted source count: `{summary['accepted_source_count']}`",
        f"- Candidate family count: `{summary['candidate_family_count']}`",
        "- Required gates: " + ", ".join(f"`{gate}`" for gate in summary["required_gates"]),
        "- Forbidden dependencies: "
        + ", ".join(f"`{dependency}`" for dependency in summary["forbidden_dependencies"]),
        f"- Option B closed: `{str(summary['option_b_closed']).lower()}`",
        (
            "- Clay Navier-Stokes promoted: "
            f"`{str(summary['clay_navier_stokes_promoted']).lower()}`"
        ),
        "",
        "## Compact O/R/C/S/L/P/G/F",
        "",
    ]
    control_card = summary["control_card"]
    lines.extend(f"- {key}: {control_card[key]}" for key in ("O", "R", "C", "S", "L", "P", "G", "F"))
    lines.extend(
        [
            "",
            "| Family | Classification | Accepted | Failed gates | Forbidden dependencies | Note |",
            "| --- | --- | --- | --- | --- | --- |",
        ]
    )
    for row in summary["rows"]:
        failed = (
            "none"
            if not row["failed_gates"]
            else ", ".join(f"`{gate}`" for gate in row["failed_gates"])
        )
        lines.append(
            "| "
            + " | ".join(
                [
                    f"`{row['family_id']}` `{row['family']}`",
                    row["classification"],
                    f"`{str(row['accepted']).lower()}`",
                    failed,
                    f"`{row['forbidden_dependencies']}`",
                    row["note"],
                ]
            )
            + " |"
        )
    lines.extend(["", summary["fail_closed_reason"]])
    return "\n".join(lines) + "\n"


def write_outputs(out_dir: Path, summary: dict[str, Any]) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / SUMMARY_NAME).write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (out_dir / ROWS_NAME).write_text(
        json.dumps(summary["rows"], indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (out_dir / REPORT_NAME).write_text(render_markdown(summary), encoding="utf-8")


def main() -> int:
    args = parse_args()
    _repo_root = args.repo_root.resolve()
    summary = build_summary()
    write_outputs(args.out_dir, summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
