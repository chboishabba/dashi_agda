#!/usr/bin/env python3
"""Sprint 99 NS viscous residence-time defeat mechanism classifier.

This deterministic ledger classifies candidate residence-time and viscous
damping defeat mechanisms. It accepts no candidate unless every required gate
is present and the candidate is free of forbidden dependencies.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint99_viscous_residence_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint99_viscous_residence_classifier")
SUMMARY_NAME = "ns_sprint99_viscous_residence_classifier_summary.json"
ROWS_NAME = "ns_sprint99_viscous_residence_classifier_rows.json"
REPORT_NAME = "ns_sprint99_viscous_residence_classifier.md"
ROUTE_DECISION = "FAIL_CLOSED_VISCOUS_RESIDENCE"

REQUIRED_GATES = (
    "positive_residence_window",
    "time_integrated_flux_surplus",
    "beats_viscous_damping",
    "leray_energy_compatible",
    "non_circular_kstar_collapse_forcing",
    "no_forbidden_dependency",
)

FORBIDDEN_DEPENDENCIES = (
    "assumed_bkm_failure",
    "assumed_serrin_failure",
    "assumed_singularity",
    "target_blowup",
    "desired_conclusion",
    "external_forcing",
    "imposed_residence_time",
    "target_kstar_collapse",
)


@dataclass(frozen=True)
class ResidenceMechanism:
    family_id: str
    family: str
    ansatz: str
    classification: str
    positive_residence_window: bool
    time_integrated_flux_surplus: bool
    beats_viscous_damping: bool
    leray_energy_compatible: bool
    non_circular_kstar_collapse_forcing: bool
    forbidden_dependencies: tuple[str, ...]
    verdict: str
    note: str

    @property
    def no_forbidden_dependency(self) -> bool:
        return len(self.forbidden_dependencies) == 0

    @property
    def gate_results(self) -> dict[str, bool]:
        return {
            "positive_residence_window": self.positive_residence_window,
            "time_integrated_flux_surplus": self.time_integrated_flux_surplus,
            "beats_viscous_damping": self.beats_viscous_damping,
            "leray_energy_compatible": self.leray_energy_compatible,
            "non_circular_kstar_collapse_forcing": self.non_circular_kstar_collapse_forcing,
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


def mechanism_families() -> list[ResidenceMechanism]:
    return [
        ResidenceMechanism(
            family_id="R1",
            family="persistent_low_mode_reservoir",
            ansatz="store transferred energy in low modes over a positive interval",
            classification="reservoir without flux surplus closure",
            positive_residence_window=True,
            time_integrated_flux_surplus=False,
            beats_viscous_damping=False,
            leray_energy_compatible=True,
            non_circular_kstar_collapse_forcing=False,
            forbidden_dependencies=("desired_conclusion",),
            verdict="reject",
            note=(
                "A persistent reservoir names the desired state, but it does not derive "
                "the signed time-integrated surplus or an independent viscous defeat."
            ),
        ),
        ResidenceMechanism(
            family_id="B1",
            family="burst_flux_window",
            ansatz="a short nonlinear burst overwhelms damping before it dissipates",
            classification="transient burst without residence control",
            positive_residence_window=False,
            time_integrated_flux_surplus=True,
            beats_viscous_damping=False,
            leray_energy_compatible=True,
            non_circular_kstar_collapse_forcing=False,
            forbidden_dependencies=(),
            verdict="reject",
            note=(
                "A burst can supply a formal flux surplus, but the candidate lacks a "
                "positive residence window and a closed comparison against viscosity."
            ),
        ),
        ResidenceMechanism(
            family_id="I1",
            family="inverse_cascade_residence",
            ansatz="inverse cascade keeps energy in low modes long enough to collapse K*",
            classification="cascade residence postulate",
            positive_residence_window=True,
            time_integrated_flux_surplus=False,
            beats_viscous_damping=False,
            leray_energy_compatible=False,
            non_circular_kstar_collapse_forcing=False,
            forbidden_dependencies=("target_kstar_collapse",),
            verdict="reject",
            note=(
                "The residence interval is tied to the target K* collapse and supplies "
                "no non-circular flux surplus or Leray-compatible construction."
            ),
        ),
        ResidenceMechanism(
            family_id="P1",
            family="pressure_trapping",
            ansatz="pressure nonlocality traps energy in low shells against diffusion",
            classification="pressure trapping sketch",
            positive_residence_window=False,
            time_integrated_flux_surplus=False,
            beats_viscous_damping=False,
            leray_energy_compatible=True,
            non_circular_kstar_collapse_forcing=False,
            forbidden_dependencies=(),
            verdict="reject",
            note=(
                "Pressure nonlocality is compatible with the equations, but this sketch "
                "does not yield a signed residence window or damping-defeat inequality."
            ),
        ),
        ResidenceMechanism(
            family_id="V1",
            family="vortex_stretching_residence",
            ansatz="vortex stretching sustains residence faster than viscosity drains it",
            classification="stretching residence heuristic",
            positive_residence_window=False,
            time_integrated_flux_surplus=False,
            beats_viscous_damping=False,
            leray_energy_compatible=True,
            non_circular_kstar_collapse_forcing=False,
            forbidden_dependencies=("target_blowup",),
            verdict="reject",
            note=(
                "Stretching is a real nonlinear channel, but this family assumes a blowup "
                "endpoint and does not close the residence or damping gates."
            ),
        ),
        ResidenceMechanism(
            family_id="T1",
            family="imposed_residence_interval",
            ansatz="choose an interval [t0,t1] where residence beats viscous loss",
            classification="imposed interval",
            positive_residence_window=True,
            time_integrated_flux_surplus=False,
            beats_viscous_damping=True,
            leray_energy_compatible=False,
            non_circular_kstar_collapse_forcing=False,
            forbidden_dependencies=("imposed_residence_time", "desired_conclusion"),
            verdict="reject",
            note=(
                "The interval is imposed rather than derived, so the damping defeat is "
                "not an admissible independent mechanism."
            ),
        ),
    ]


def build_summary() -> dict[str, Any]:
    rows = [family.row() for family in mechanism_families()]
    accepted = [row for row in rows if row["accepted"]]
    fail_closed = not accepted
    return {
        "contract": CONTRACT,
        "complete": False,
        "proof_claimed": False,
        "scope": (
            "deterministic classifier for candidate residence-time and viscous damping "
            "defeat mechanisms"
        ),
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
        "sprint99_viscous_residence_closed": False,
        "fail_closed_reason": (
            "No candidate family satisfies every residence-time and viscous damping gate "
            "without a forbidden dependency."
        ),
        "computed_fail_closed_from_rows": fail_closed,
        "rows": rows,
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 99 Viscous Residence Classifier",
        "",
        f"- Contract: `{summary['contract']}`",
        "- Scope: deterministic residence-time and viscous damping defeat classification.",
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
