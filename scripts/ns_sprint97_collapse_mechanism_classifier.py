#!/usr/bin/env python3
"""Sprint 97 NS collapse mechanism family classifier.

This is a deterministic fail-closed ledger. It classifies named candidate
mechanism families against the Sprint 97 collapse gates and accepts no source
unless every required gate is supplied without a forbidden dependency.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint97_collapse_mechanism_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint97_collapse_mechanism_classifier")
SUMMARY_NAME = "ns_sprint97_collapse_mechanism_classifier_summary.json"
ROWS_NAME = "ns_sprint97_collapse_mechanism_classifier_rows.json"
REPORT_NAME = "ns_sprint97_collapse_mechanism_classifier.md"

REQUIRED_GATES = (
    "finite_time_kstar_to_zero",
    "low_mode_energy_concentration_dynamics",
    "viscous_damping_defeat_estimate",
    "leray_compatible_trajectory",
    "excludes_option_c_lower_bound",
    "singularity_extraction_without_bkm_or_serrin",
    "no_forbidden_dependency",
)

FORBIDDEN_DEPENDENCIES = (
    "assumed_bkm_failure",
    "assumed_serrin_failure",
    "assumed_singularity",
    "blowup_construction_assumed",
    "clay_claim",
    "conditional_regular_negation",
    "desired_conclusion",
    "h1_continuation_failure_assumed",
    "option_c_lower_bound_negated_without_mechanism",
    "self_similarity_imposed_as_proof",
    "target_absorption",
    "target_blowup",
)


@dataclass(frozen=True)
class MechanismFamily:
    family_id: str
    family: str
    ansatz: str
    classification: str
    finite_time_kstar_to_zero: bool
    low_mode_energy_concentration_dynamics: bool
    viscous_damping_defeat_estimate: bool
    leray_compatible_trajectory: bool
    excludes_option_c_lower_bound: bool
    singularity_extraction_without_bkm_or_serrin: bool
    forbidden_dependencies: tuple[str, ...]
    verdict: str
    note: str

    @property
    def no_forbidden_dependency(self) -> bool:
        return len(self.forbidden_dependencies) == 0

    @property
    def gate_results(self) -> dict[str, bool]:
        return {
            "finite_time_kstar_to_zero": self.finite_time_kstar_to_zero,
            "low_mode_energy_concentration_dynamics": self.low_mode_energy_concentration_dynamics,
            "viscous_damping_defeat_estimate": self.viscous_damping_defeat_estimate,
            "leray_compatible_trajectory": self.leray_compatible_trajectory,
            "excludes_option_c_lower_bound": self.excludes_option_c_lower_bound,
            "singularity_extraction_without_bkm_or_serrin": (
                self.singularity_extraction_without_bkm_or_serrin
            ),
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


def mechanism_families() -> list[MechanismFamily]:
    return [
        MechanismFamily(
            family_id="C0",
            family="constant lower bound",
            ansatz="K*(t) >= k0 > 0",
            classification="non-collapse lower-bound family",
            finite_time_kstar_to_zero=False,
            low_mode_energy_concentration_dynamics=False,
            viscous_damping_defeat_estimate=False,
            leray_compatible_trajectory=True,
            excludes_option_c_lower_bound=False,
            singularity_extraction_without_bkm_or_serrin=False,
            forbidden_dependencies=(),
            verdict="reject",
            note=(
                "This family preserves a positive K* floor, so it cannot supply finite-time "
                "K* collapse or exclude the lower-bound alternative."
            ),
        ),
        MechanismFamily(
            family_id="A1",
            family="pure algebraic collapse",
            ansatz="K*(t) = c (T - t)^alpha, alpha > 0",
            classification="rate ansatz without dynamics",
            finite_time_kstar_to_zero=True,
            low_mode_energy_concentration_dynamics=False,
            viscous_damping_defeat_estimate=False,
            leray_compatible_trajectory=False,
            excludes_option_c_lower_bound=False,
            singularity_extraction_without_bkm_or_serrin=False,
            forbidden_dependencies=(),
            verdict="reject",
            note=(
                "The rate tends to zero but supplies no independent concentration dynamics, "
                "viscous defeat estimate, Leray trajectory, or singularity extraction."
            ),
        ),
        MechanismFamily(
            family_id="L1",
            family="logarithmic collapse",
            ansatz="K*(t) = c / log(e + 1/(T - t))",
            classification="slow rate ansatz without dynamics",
            finite_time_kstar_to_zero=True,
            low_mode_energy_concentration_dynamics=False,
            viscous_damping_defeat_estimate=False,
            leray_compatible_trajectory=False,
            excludes_option_c_lower_bound=False,
            singularity_extraction_without_bkm_or_serrin=False,
            forbidden_dependencies=(),
            verdict="reject",
            note=(
                "The logarithmic profile is still only a prescribed rate; it does not "
                "derive the required energy-transfer and damping gates."
            ),
        ),
        MechanismFamily(
            family_id="O1",
            family="oscillatory ansatz",
            ansatz="K*(t) = c (T - t)^alpha (1 + beta sin(omega log(1/(T - t))))",
            classification="oscillatory rate ansatz",
            finite_time_kstar_to_zero=True,
            low_mode_energy_concentration_dynamics=False,
            viscous_damping_defeat_estimate=False,
            leray_compatible_trajectory=False,
            excludes_option_c_lower_bound=False,
            singularity_extraction_without_bkm_or_serrin=False,
            forbidden_dependencies=("assumed_singularity",),
            verdict="reject",
            note=(
                "Oscillation does not provide a closed low-mode transfer mechanism and "
                "relies on the singular endpoint as an input."
            ),
        ),
        MechanismFamily(
            family_id="S1",
            family="imposed self-similar ansatz",
            ansatz="u(x,t) = (T - t)^(-a) U((x - x0)/(T - t)^b)",
            classification="imposed self-similar profile",
            finite_time_kstar_to_zero=True,
            low_mode_energy_concentration_dynamics=False,
            viscous_damping_defeat_estimate=False,
            leray_compatible_trajectory=False,
            excludes_option_c_lower_bound=False,
            singularity_extraction_without_bkm_or_serrin=False,
            forbidden_dependencies=("self_similarity_imposed_as_proof", "target_blowup"),
            verdict="reject",
            note=(
                "A profile imposed at the outset is not an extracted Leray-compatible "
                "trajectory and is rejected as a forbidden dependency."
            ),
        ),
        MechanismFamily(
            family_id="E1",
            family="energy-transfer ODE sketch",
            ansatz="dE_low/dt = Phi_high_to_low(t) - D_low(t)",
            classification="formal transfer sketch",
            finite_time_kstar_to_zero=False,
            low_mode_energy_concentration_dynamics=True,
            viscous_damping_defeat_estimate=False,
            leray_compatible_trajectory=False,
            excludes_option_c_lower_bound=False,
            singularity_extraction_without_bkm_or_serrin=False,
            forbidden_dependencies=("target_absorption",),
            verdict="reject",
            note=(
                "The ODE sketch names a transfer channel but lacks a quantitative damping "
                "defeat estimate, K* collapse law, Leray construction, and extraction bridge."
            ),
        ),
    ]


def build_summary() -> dict[str, Any]:
    rows = [family.row() for family in mechanism_families()]
    accepted = [row for row in rows if row["accepted"]]
    all_gates_true = bool(accepted)
    no_forbidden_deps = all(row["no_forbidden_dependency"] for row in accepted)
    fail_closed = not (all_gates_true and no_forbidden_deps)
    return {
        "contract": CONTRACT,
        "complete": False,
        "proof_claimed": False,
        "scope": "deterministic classifier for Sprint 97 candidate K* collapse mechanism families",
        "fail_closed": fail_closed,
        "route_decision": "FAIL_CLOSED" if fail_closed else "MECHANISM_ACCEPTED",
        "final_decision": "FAIL_CLOSED" if fail_closed else "REVIEW_ACCEPTED_MECHANISM",
        "accepted_source_count": 0 if fail_closed else len(accepted),
        "candidate_family_count": len(rows),
        "required_gates": list(REQUIRED_GATES),
        "forbidden_dependencies": list(FORBIDDEN_DEPENDENCIES),
        "accepted_families": [] if fail_closed else [row["family_id"] for row in accepted],
        "rejected_families": [row["family_id"] for row in rows if not row["accepted"]],
        "clay_navier_stokes_promoted": False,
        "option_b_closed": False if fail_closed else bool(accepted),
        "sprint97_mechanism_closed": False if fail_closed else bool(accepted),
        "rows": rows,
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 97 Collapse Mechanism Classifier",
        "",
        f"- Contract: `{summary['contract']}`",
        "- Scope: deterministic classification of candidate K* collapse mechanism families.",
        "- Proof claimed: `false`",
        f"- Fail closed: `{str(summary['fail_closed']).lower()}`",
        f"- Accepted source count: `{summary['accepted_source_count']}`",
        f"- Candidate family count: `{summary['candidate_family_count']}`",
        f"- Final decision: `{summary['final_decision']}`",
        "- Required gates: " + ", ".join(f"`{gate}`" for gate in summary["required_gates"]),
        "- Forbidden dependencies: "
        + ", ".join(f"`{dependency}`" for dependency in summary["forbidden_dependencies"]),
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
                    f"`{row['family_id']}` {row['family']}",
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
                "The classifier is fail-closed because no mechanism family satisfies every "
                "required gate without a forbidden dependency."
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
