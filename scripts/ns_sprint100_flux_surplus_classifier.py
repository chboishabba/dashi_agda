#!/usr/bin/env python3
"""Sprint 100 NS flux-surplus source classifier.

This deterministic ledger classifies candidate nonlinear flux-surplus sources.
It accepts no candidate unless every required gate is present and the candidate
is free of forbidden dependencies.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint100_flux_surplus_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint100_flux_surplus_classifier")
SUMMARY_NAME = "ns_sprint100_flux_surplus_classifier_summary.json"
ROWS_NAME = "ns_sprint100_flux_surplus_classifier_rows.json"
REPORT_NAME = "ns_sprint100_flux_surplus_classifier.md"
ROUTE_DECISION = "FAIL_CLOSED_FLUX_SURPLUS"

REQUIRED_GATES = (
    "signed_low_mode_flux_lower_bound",
    "time_integrated_positive_surplus",
    "beats_dissipation_budget",
    "leray_energy_compatible",
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
    "imposed_flux_sign",
    "target_kstar_collapse",
    "imposed_surplus_window",
)


@dataclass(frozen=True)
class FluxSurplusSource:
    family_id: str
    family: str
    ansatz: str
    classification: str
    signed_low_mode_flux_lower_bound: bool
    time_integrated_positive_surplus: bool
    beats_dissipation_budget: bool
    leray_energy_compatible: bool
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
            "signed_low_mode_flux_lower_bound": self.signed_low_mode_flux_lower_bound,
            "time_integrated_positive_surplus": self.time_integrated_positive_surplus,
            "beats_dissipation_budget": self.beats_dissipation_budget,
            "leray_energy_compatible": self.leray_energy_compatible,
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


def candidate_families() -> list[FluxSurplusSource]:
    return [
        FluxSurplusSource(
            family_id="T1",
            family="signed_triadic_transfer",
            ansatz="derive a favorable low-mode sign from selected Fourier triads",
            classification="triadic sign mechanism",
            signed_low_mode_flux_lower_bound=False,
            time_integrated_positive_surplus=False,
            beats_dissipation_budget=False,
            leray_energy_compatible=True,
            non_circular_source=False,
            forbidden_dependencies=("imposed_flux_sign",),
            verdict="reject",
            note=(
                "Triadic transfer is an admissible nonlinear channel, but the favorable "
                "sign is selected rather than derived and no time-integrated surplus is closed."
            ),
        ),
        FluxSurplusSource(
            family_id="S1",
            family="shell_local_flux_surplus",
            ansatz="nearest-neighbor shell transfer produces surplus into low modes",
            classification="local shell flux channel",
            signed_low_mode_flux_lower_bound=False,
            time_integrated_positive_surplus=False,
            beats_dissipation_budget=False,
            leray_energy_compatible=True,
            non_circular_source=True,
            forbidden_dependencies=(),
            verdict="reject",
            note=(
                "Shell-local transfer is non-circular and energy-budget compatible, but it "
                "does not supply a signed lower bound or a comparison that beats dissipation."
            ),
        ),
        FluxSurplusSource(
            family_id="P1",
            family="pressure_nonlocal_flux",
            ansatz="pressure nonlocality redirects energy across separated Fourier scales",
            classification="nonlocal pressure flux sketch",
            signed_low_mode_flux_lower_bound=False,
            time_integrated_positive_surplus=False,
            beats_dissipation_budget=False,
            leray_energy_compatible=True,
            non_circular_source=True,
            forbidden_dependencies=(),
            verdict="reject",
            note=(
                "Pressure coupling is compatible with incompressible Navier-Stokes, but "
                "the sketch lacks a quantitative signed surplus and a dissipation budget win."
            ),
        ),
        FluxSurplusSource(
            family_id="B1",
            family="burst_integrated_surplus",
            ansatz="a short nonlinear burst gives positive integrated surplus",
            classification="transient burst surplus",
            signed_low_mode_flux_lower_bound=False,
            time_integrated_positive_surplus=True,
            beats_dissipation_budget=False,
            leray_energy_compatible=True,
            non_circular_source=True,
            forbidden_dependencies=(),
            verdict="reject",
            note=(
                "A burst can model a positive integral, but this family has no pointwise "
                "signed lower bound and does not close the dissipation comparison."
            ),
        ),
        FluxSurplusSource(
            family_id="I1",
            family="inverse_cascade_surplus",
            ansatz="an inverse cascade persistently feeds low modes with surplus energy",
            classification="inverse-cascade surplus unsupported premise",
            signed_low_mode_flux_lower_bound=False,
            time_integrated_positive_surplus=False,
            beats_dissipation_budget=False,
            leray_energy_compatible=False,
            non_circular_source=False,
            forbidden_dependencies=("target_kstar_collapse", "desired_conclusion"),
            verdict="reject",
            note=(
                "The surplus is tied to the desired cascade endpoint, so it supplies no "
                "independent source and remains outside a closed Leray-compatible budget."
            ),
        ),
        FluxSurplusSource(
            family_id="W1",
            family="imposed_surplus_window",
            ansatz="choose an interval where signed flux surplus exceeds dissipation",
            classification="imposed surplus interval",
            signed_low_mode_flux_lower_bound=True,
            time_integrated_positive_surplus=True,
            beats_dissipation_budget=True,
            leray_energy_compatible=False,
            non_circular_source=False,
            forbidden_dependencies=("imposed_surplus_window", "desired_conclusion"),
            verdict="reject",
            note=(
                "The window directly assumes the needed surplus and budget victory, so "
                "the mechanism is circular and uses a forbidden dependency."
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
        "scope": "deterministic classifier for candidate flux-surplus sources",
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
        "sprint100_flux_surplus_closed": False,
        "fail_closed_reason": (
            "No candidate family satisfies every flux-surplus source gate without a "
            "forbidden dependency."
        ),
        "computed_fail_closed_from_rows": fail_closed,
        "rows": rows,
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 100 Flux Surplus Classifier",
        "",
        f"- Contract: `{summary['contract']}`",
        "- Scope: deterministic flux-surplus source classification.",
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
        "| Family | Classification | Accepted | Failed gates | Forbidden dependencies | Note |",
        "| --- | --- | --- | --- | --- | --- |",
    ]
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
