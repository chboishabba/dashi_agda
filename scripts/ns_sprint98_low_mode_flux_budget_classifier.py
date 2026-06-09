#!/usr/bin/env python3
"""Sprint 98 NS low-mode flux budget mechanism classifier.

This deterministic ledger classifies candidate mechanisms for concentrating
energy in low Fourier modes. It accepts no candidate unless every required
budget gate is present and the candidate is free of forbidden dependencies.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint98_low_mode_flux_budget_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint98_low_mode_flux_budget_classifier")
SUMMARY_NAME = "ns_sprint98_low_mode_flux_budget_classifier_summary.json"
ROWS_NAME = "ns_sprint98_low_mode_flux_budget_classifier_rows.json"
REPORT_NAME = "ns_sprint98_low_mode_flux_budget_classifier.md"

REQUIRED_GATES = (
    "quantitative_low_mode_flux_lower_bound",
    "residence_time_against_viscosity",
    "leray_energy_budget_compatible",
    "coherent_inverse_cascade",
    "non_circular_kstar_forcing",
    "no_forbidden_dependency",
)

FORBIDDEN_DEPENDENCIES = (
    "assumed_bkm_failure",
    "assumed_serrin_failure",
    "assumed_singularity",
    "target_blowup",
    "desired_conclusion",
    "external_forcing",
    "imposed_inverse_cascade",
    "target_kstar_collapse",
)


@dataclass(frozen=True)
class LowModeMechanism:
    family_id: str
    family: str
    ansatz: str
    classification: str
    quantitative_low_mode_flux_lower_bound: bool
    residence_time_against_viscosity: bool
    leray_energy_budget_compatible: bool
    coherent_inverse_cascade: bool
    non_circular_kstar_forcing: bool
    forbidden_dependencies: tuple[str, ...]
    verdict: str
    note: str

    @property
    def no_forbidden_dependency(self) -> bool:
        return len(self.forbidden_dependencies) == 0

    @property
    def gate_results(self) -> dict[str, bool]:
        return {
            "quantitative_low_mode_flux_lower_bound": (
                self.quantitative_low_mode_flux_lower_bound
            ),
            "residence_time_against_viscosity": self.residence_time_against_viscosity,
            "leray_energy_budget_compatible": self.leray_energy_budget_compatible,
            "coherent_inverse_cascade": self.coherent_inverse_cascade,
            "non_circular_kstar_forcing": self.non_circular_kstar_forcing,
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


def mechanism_families() -> list[LowModeMechanism]:
    return [
        LowModeMechanism(
            family_id="F1",
            family="direct_low_mode_forcing",
            ansatz="inject energy directly into |k| <= K_low",
            classification="forced low-mode reservoir",
            quantitative_low_mode_flux_lower_bound=True,
            residence_time_against_viscosity=True,
            leray_energy_budget_compatible=False,
            coherent_inverse_cascade=False,
            non_circular_kstar_forcing=False,
            forbidden_dependencies=("external_forcing",),
            verdict="reject",
            note=(
                "Direct injection can name a low-mode flux, but it is not an unforced "
                "Leray Navier-Stokes mechanism and uses forbidden external forcing."
            ),
        ),
        LowModeMechanism(
            family_id="I1",
            family="inverse_cascade_ansatz",
            ansatz="postulate persistent transfer from high shells to low shells",
            classification="imposed inverse-cascade narrative",
            quantitative_low_mode_flux_lower_bound=False,
            residence_time_against_viscosity=False,
            leray_energy_budget_compatible=False,
            coherent_inverse_cascade=False,
            non_circular_kstar_forcing=False,
            forbidden_dependencies=("imposed_inverse_cascade", "target_kstar_collapse"),
            verdict="reject",
            note=(
                "A cascade direction asserted as an ansatz supplies no quantitative lower "
                "bound, residence estimate, or non-circular K* forcing."
            ),
        ),
        LowModeMechanism(
            family_id="S1",
            family="shell_local_transfer",
            ansatz="nearest-neighbor shell flux moves energy across adjacent bands",
            classification="local shell transfer channel",
            quantitative_low_mode_flux_lower_bound=False,
            residence_time_against_viscosity=False,
            leray_energy_budget_compatible=True,
            coherent_inverse_cascade=False,
            non_circular_kstar_forcing=False,
            forbidden_dependencies=(),
            verdict="reject",
            note=(
                "Local transfer is energy-budget compatible, but it does not force a "
                "sustained inverse cascade or produce a low-mode flux lower bound."
            ),
        ),
        LowModeMechanism(
            family_id="P1",
            family="pressure_nonlocal_transfer",
            ansatz="pressure couples separated scales and redirects energy to low modes",
            classification="nonlocal coupling sketch",
            quantitative_low_mode_flux_lower_bound=False,
            residence_time_against_viscosity=False,
            leray_energy_budget_compatible=True,
            coherent_inverse_cascade=False,
            non_circular_kstar_forcing=False,
            forbidden_dependencies=(),
            verdict="reject",
            note=(
                "Pressure nonlocality can be compatible with the equations, but the "
                "candidate lacks a signed quantitative flux lower bound and residence time."
            ),
        ),
        LowModeMechanism(
            family_id="V1",
            family="vortex_stretching_concentration",
            ansatz="stretching intensifies vorticity and concentrates energy into low modes",
            classification="stretching-to-concentration heuristic",
            quantitative_low_mode_flux_lower_bound=False,
            residence_time_against_viscosity=False,
            leray_energy_budget_compatible=True,
            coherent_inverse_cascade=False,
            non_circular_kstar_forcing=False,
            forbidden_dependencies=("target_blowup",),
            verdict="reject",
            note=(
                "Stretching is a valid nonlinear channel, but this family does not close "
                "the low-mode flux budget and relies on a target blowup endpoint."
            ),
        ),
        LowModeMechanism(
            family_id="E1",
            family="energy_transfer_ode",
            ansatz="dE_low/dt = Phi_to_low(t) - 2 nu ||grad u_low||_2^2",
            classification="formal low-mode ODE",
            quantitative_low_mode_flux_lower_bound=False,
            residence_time_against_viscosity=False,
            leray_energy_budget_compatible=True,
            coherent_inverse_cascade=False,
            non_circular_kstar_forcing=False,
            forbidden_dependencies=("desired_conclusion",),
            verdict="reject",
            note=(
                "The ODE names the budget terms but leaves the required lower bound and "
                "anti-viscous residence estimate as assumptions."
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
        "scope": "deterministic classifier for low-mode energy concentration mechanisms",
        "fail_closed": True if fail_closed else False,
        "route_decision": (
            "FAIL_CLOSED_LOW_MODE_FLUX_BUDGET"
            if fail_closed
            else "LOW_MODE_FLUX_BUDGET_MECHANISM_ACCEPTED"
        ),
        "final_decision": (
            "FAIL_CLOSED_LOW_MODE_FLUX_BUDGET"
            if fail_closed
            else "REVIEW_ACCEPTED_LOW_MODE_FLUX_MECHANISM"
        ),
        "accepted_source_count": 0 if fail_closed else len(accepted),
        "candidate_family_count": len(rows),
        "required_gates": list(REQUIRED_GATES),
        "forbidden_dependencies": list(FORBIDDEN_DEPENDENCIES),
        "accepted_families": [] if fail_closed else [row["family"] for row in accepted],
        "rejected_families": [row["family"] for row in rows if not row["accepted"]],
        "clay_navier_stokes_promoted": False,
        "option_b_closed": False,
        "sprint98_low_mode_flux_budget_closed": False if fail_closed else bool(accepted),
        "rows": rows,
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 98 Low-Mode Flux Budget Classifier",
        "",
        f"- Contract: `{summary['contract']}`",
        "- Scope: deterministic low-mode energy concentration mechanism classification.",
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
    lines.extend(
        [
            "",
            (
                "The classifier is fail-closed because no candidate family satisfies every "
                "low-mode flux budget gate without a forbidden dependency."
            ),
        ]
    )
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
