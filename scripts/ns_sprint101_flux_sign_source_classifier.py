#!/usr/bin/env python3
"""Sprint 101 NS flux-sign source classifier.

This deterministic fail-closed ledger classifies candidate mechanisms for a
signed low-mode flux lower bound. A candidate is accepted only when every
required gate is supplied and no forbidden dependency is present.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint101_flux_sign_source_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint101_flux_sign_source_classifier")
SUMMARY_NAME = "ns_sprint101_flux_sign_source_classifier_summary.json"
ROWS_NAME = "ns_sprint101_flux_sign_source_classifier_rows.json"
REPORT_NAME = "ns_sprint101_flux_sign_source_classifier.md"
ROUTE_DECISION = "FAIL_CLOSED_FLUX_SIGN_SOURCE"

REQUIRED_GATES = (
    "triadic_sign_coherence",
    "low_mode_projection_sign_control",
    "cancellation_defect_bound",
    "pressure_transport_sign_accounting",
    "leray_energy_compatible",
    "non_circular_flux_sign_source",
    "no_forbidden_dependency",
)

FORBIDDEN_DEPENDENCIES = (
    "assumed_bkm_failure",
    "assumed_serrin_failure",
    "assumed_singularity",
    "target_blowup",
    "desired_conclusion",
    "external_forcing",
    "imposed_flux_sign",
    "imposed_triad_phase",
    "target_kstar_collapse",
    "imposed_surplus_window",
)


@dataclass(frozen=True)
class FluxSignSource:
    family_id: str
    family: str
    ansatz: str
    classification: str
    triadic_sign_coherence: bool
    low_mode_projection_sign_control: bool
    cancellation_defect_bound: bool
    pressure_transport_sign_accounting: bool
    leray_energy_compatible: bool
    non_circular_flux_sign_source: bool
    forbidden_dependencies: tuple[str, ...]
    verdict: str
    note: str

    @property
    def no_forbidden_dependency(self) -> bool:
        return len(self.forbidden_dependencies) == 0

    @property
    def gate_results(self) -> dict[str, bool]:
        return {
            "triadic_sign_coherence": self.triadic_sign_coherence,
            "low_mode_projection_sign_control": self.low_mode_projection_sign_control,
            "cancellation_defect_bound": self.cancellation_defect_bound,
            "pressure_transport_sign_accounting": self.pressure_transport_sign_accounting,
            "leray_energy_compatible": self.leray_energy_compatible,
            "non_circular_flux_sign_source": self.non_circular_flux_sign_source,
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


def candidate_families() -> list[FluxSignSource]:
    return [
        FluxSignSource(
            family_id="T1",
            family="coherent_triad_alignment",
            ansatz="align selected low/high/high triads so their transfer has a favorable sign",
            classification="phase-selected triadic sign sketch",
            triadic_sign_coherence=False,
            low_mode_projection_sign_control=False,
            cancellation_defect_bound=False,
            pressure_transport_sign_accounting=False,
            leray_energy_compatible=True,
            non_circular_flux_sign_source=False,
            forbidden_dependencies=("imposed_triad_phase", "imposed_flux_sign"),
            verdict="reject",
            note=(
                "A favorable triad orientation is selected rather than derived; the "
                "candidate lacks a cancellation-defect bound and does not account for "
                "pressure transport in the projected low-mode budget."
            ),
        ),
        FluxSignSource(
            family_id="S1",
            family="shell_local_sign_bias",
            ansatz="nearest-neighbor shell interactions carry a persistent sign bias into low modes",
            classification="shell-local sign-bias heuristic",
            triadic_sign_coherence=False,
            low_mode_projection_sign_control=False,
            cancellation_defect_bound=False,
            pressure_transport_sign_accounting=False,
            leray_energy_compatible=True,
            non_circular_flux_sign_source=True,
            forbidden_dependencies=(),
            verdict="reject",
            note=(
                "Shell locality is compatible with the Leray energy ledger, but locality "
                "does not determine the sign after summing interacting triads and projected "
                "cancellations remain uncontrolled."
            ),
        ),
        FluxSignSource(
            family_id="P1",
            family="pressure_projection_sign",
            ansatz="the Leray pressure projection fixes the low-mode transfer orientation",
            classification="pressure-projection sign assertion",
            triadic_sign_coherence=False,
            low_mode_projection_sign_control=False,
            cancellation_defect_bound=False,
            pressure_transport_sign_accounting=False,
            leray_energy_compatible=True,
            non_circular_flux_sign_source=True,
            forbidden_dependencies=(),
            verdict="reject",
            note=(
                "The pressure projection is part of the equations, but it is not a signed "
                "source by itself; the candidate does not separate pressure transport from "
                "nonlinear transfer or bound the residual cancellation defect."
            ),
        ),
        FluxSignSource(
            family_id="H1",
            family="helical_alignment_sign",
            ansatz="helical polarization of modes enforces a favorable transfer sign",
            classification="helical sign-alignment mechanism",
            triadic_sign_coherence=False,
            low_mode_projection_sign_control=False,
            cancellation_defect_bound=False,
            pressure_transport_sign_accounting=False,
            leray_energy_compatible=True,
            non_circular_flux_sign_source=False,
            forbidden_dependencies=("imposed_triad_phase", "desired_conclusion"),
            verdict="reject",
            note=(
                "Helical decomposition can expose transfer channels, but the persistent "
                "alignment is imposed as the desired sign conclusion and is not propagated "
                "by a closed Leray-compatible mechanism."
            ),
        ),
        FluxSignSource(
            family_id="B1",
            family="intermittent_burst_sign",
            ansatz="short nonlinear bursts create intervals with favorable low-mode flux sign",
            classification="transient burst sign narrative",
            triadic_sign_coherence=False,
            low_mode_projection_sign_control=False,
            cancellation_defect_bound=False,
            pressure_transport_sign_accounting=False,
            leray_energy_compatible=True,
            non_circular_flux_sign_source=True,
            forbidden_dependencies=("imposed_surplus_window",),
            verdict="reject",
            note=(
                "A burst interval can be named, but the signed window is imposed rather "
                "than derived and no uniform lower bound survives cancellation across the "
                "low-mode projection."
            ),
        ),
        FluxSignSource(
            family_id="F1",
            family="imposed_flux_orientation",
            ansatz="prescribe the orientation of flux so low modes receive a signed lower bound",
            classification="forbidden imposed sign source",
            triadic_sign_coherence=True,
            low_mode_projection_sign_control=True,
            cancellation_defect_bound=False,
            pressure_transport_sign_accounting=False,
            leray_energy_compatible=False,
            non_circular_flux_sign_source=False,
            forbidden_dependencies=("imposed_flux_sign", "external_forcing", "desired_conclusion"),
            verdict="reject",
            note=(
                "The candidate directly prescribes the needed sign orientation, so any "
                "apparent sign control is circular and outside the unforced Navier-Stokes "
                "closure target."
            ),
        ),
    ]


def build_summary() -> dict[str, Any]:
    rows = [family.row() for family in candidate_families()]
    accepted = [row for row in rows if row["accepted"]]
    fail_closed = not accepted
    return {
        "contract": CONTRACT,
        "complete": False,
        "proof_claimed": False,
        "scope": "deterministic classifier for candidate signed low-mode flux lower-bound mechanisms",
        "fail_closed": True,
        "route_decision": ROUTE_DECISION,
        "final_decision": ROUTE_DECISION,
        "accepted_source_count": 0,
        "candidate_family_count": len(rows),
        "required_gates": list(REQUIRED_GATES),
        "forbidden_dependencies": list(FORBIDDEN_DEPENDENCIES),
        "accepted_families": [],
        "rejected_families": [row["family"] for row in rows],
        "option_b_closed": False,
        "clay_navier_stokes_promoted": False,
        "sprint101_flux_sign_source_closed": False,
        "fail_closed_reason": (
            "No candidate family supplies a non-circular signed low-mode flux lower-bound "
            "source with all required sign, cancellation, pressure-accounting, Leray, and "
            "dependency gates closed."
        ),
        "computed_fail_closed_from_rows": fail_closed,
        "control_card": {
            "O": "classify candidate signed low-mode flux lower-bound mechanisms",
            "R": "all seven gates must pass and forbidden dependencies must be absent",
            "C": "single deterministic Python ledger emitting JSON and Markdown",
            "S": "six named candidate families evaluated in fixed order",
            "L": "acceptance is the conjunction of gate_results",
            "P": ROUTE_DECISION,
            "G": "Option B remains open; Clay Navier-Stokes is not promoted",
            "F": "all candidates are rejected with concrete failed gates or dependencies",
        },
        "rows": rows,
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 101 Flux Sign Source Classifier",
        "",
        f"- Contract: `{summary['contract']}`",
        "- Scope: deterministic signed low-mode flux lower-bound source classification.",
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
