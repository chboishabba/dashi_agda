#!/usr/bin/env python3
"""Sprint 138 transport commutator budget emitter.

This deterministic emitter records the transport commutator terms in the
Sprint 137 barrier equation for ``v = partial_z u1``:

    D_t v = nu Ltilde v + 2 v partial_z psi1 + 2 u1 partial_z^2 psi1
            - (partial_z u^r) partial_r u1 - (partial_z u^z) v.

The artifact is intentionally fail-closed.  It separates the homogeneous
``v`` terms at a first positive maximum from the nonhomogeneous commutator
``-(partial_z u^r) partial_r u1``, records why incompressibility alone does
not dominate it, and keeps logarithmic Biot-Savart strain loss as an open
hazard.  The decision is not a Clay Navier-Stokes promotion.
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint138_transport_commutator_budget"
GATE = "TransportCommutatorDominationForVBarrier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint138_transport_commutator_budget")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"

VARIABLES = {
    "u1": "u^theta / r",
    "omega1": "omega^theta / r",
    "psi1": "psi^theta / r",
    "v": "partial_z u1",
    "Ltilde": "partial_r^2 + (3/r) partial_r + partial_z^2",
    "Dt": "partial_t + u^r partial_r + u^z partial_z",
}

U1_EQUATION = "D_t u1 = 2 u1 partial_z psi1 + nu Ltilde u1"
V_BARRIER_EQUATION = (
    "D_t v = nu Ltilde v + 2 v partial_z psi1 + 2 u1 partial_z^2 psi1 "
    "- (partial_z u^r) partial_r u1 - (partial_z u^z) v"
)
FIRST_POSITIVE_MAX = (
    "At the first interior positive maximum of v, v>0, "
    "partial_r v=partial_z v=0, and Ltilde v<=0."
)
COMMUTATOR_DECISION = "commutator_domination_open"
ROUTE_DECISION = "fail_closed_no_global_barrier"

REQUIRED_ROW_IDS = {
    "barrier_equation_inventory",
    "homogeneous_v_terms_first_positive_max",
    "nonhomogeneous_radial_commutator",
    "incompressibility_relation_limitations",
    "log_biot_savart_strain_hazard",
    "domination_hypothesis_pointwise_sign",
    "domination_hypothesis_integrated_margin",
    "current_fail_closed_status",
}


@dataclass(frozen=True)
class CommutatorBudgetRow:
    row_id: str
    gate: str
    term_class: str
    term_or_relation: str
    status: str
    role_at_first_positive_max: str
    budget_effect: str
    support: tuple[str, ...]
    missing_evidence: tuple[str, ...]
    domination_required: bool
    domination_available: bool
    global_barrier_closed: bool
    clay_navier_stokes_promoted: bool

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row["support"] = list(self.support)
        row["missing_evidence"] = list(self.missing_evidence)
        return row


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def build_rows() -> list[dict[str, Any]]:
    rows = [
        CommutatorBudgetRow(
            row_id="barrier_equation_inventory",
            gate=GATE,
            term_class="equation_inventory",
            term_or_relation=V_BARRIER_EQUATION,
            status="encoded",
            role_at_first_positive_max=(
                "Defines the exact local budget to be tested at the first "
                "positive maximum of v."
            ),
            budget_effect=(
                "Diffusion is nonpositive; homogeneous v terms are linear in "
                "the positive maximum; two nonhomogeneous terms remain: "
                "2 u1 partial_z^2 psi1 and -(partial_z u^r) partial_r u1."
            ),
            support=(
                "Sprint137 axial monotonicity gate",
                U1_EQUATION,
                FIRST_POSITIVE_MAX,
            ),
            missing_evidence=(),
            domination_required=True,
            domination_available=False,
            global_barrier_closed=False,
            clay_navier_stokes_promoted=False,
        ),
        CommutatorBudgetRow(
            row_id="homogeneous_v_terms_first_positive_max",
            gate=GATE,
            term_class="homogeneous_v",
            term_or_relation="2 v partial_z psi1 - (partial_z u^z) v",
            status="linear_growth_not_obstruction_by_itself",
            role_at_first_positive_max=(
                "At v>0 these terms are proportional to the maximum value of "
                "v, not independent positive forcing."
            ),
            budget_effect=(
                "They can be placed in a Gronwall coefficient if the "
                "coefficient partial_z psi1 and partial_z u^z is time "
                "integrable along the barrier window."
            ),
            support=(
                "first positive maximum geometry",
                "standard parabolic barrier accounting",
            ),
            missing_evidence=(
                "uniform time-integrable strain coefficient without losing a "
                "logarithmic factor",
            ),
            domination_required=True,
            domination_available=False,
            global_barrier_closed=False,
            clay_navier_stokes_promoted=False,
        ),
        CommutatorBudgetRow(
            row_id="nonhomogeneous_radial_commutator",
            gate=GATE,
            term_class="nonhomogeneous_commutator",
            term_or_relation="-(partial_z u^r) partial_r u1",
            status="open_hazard",
            role_at_first_positive_max=(
                "This term does not contain v and therefore can inject a "
                "positive source at the first crossing even when v is just "
                "becoming positive."
            ),
            budget_effect=(
                "A local v barrier needs either a sign rule for "
                "-(partial_z u^r) partial_r u1 or a domination inequality "
                "against the favorable concavity/source/diffusion margin."
            ),
            support=(
                "transport commutator from differentiating u^r partial_r u1",
                V_BARRIER_EQUATION,
            ),
            missing_evidence=(
                "pointwise sign of partial_z u^r times partial_r u1",
                "scale-uniform upper bound absorbed by negative terms",
                "structural cancellation with 2 u1 partial_z^2 psi1",
            ),
            domination_required=True,
            domination_available=False,
            global_barrier_closed=False,
            clay_navier_stokes_promoted=False,
        ),
        CommutatorBudgetRow(
            row_id="incompressibility_relation_limitations",
            gate=GATE,
            term_class="constraint_limitation",
            term_or_relation=(
                "partial_r u^r + u^r/r + partial_z u^z = 0; "
                "partial_z^2 u^z = -partial_z partial_r u^r - partial_z(u^r/r)"
            ),
            status="insufficient_for_domination",
            role_at_first_positive_max=(
                "Incompressibility relates components of the strain but does "
                "not determine the sign of partial_z u^r or its correlation "
                "with partial_r u1 at the crossing."
            ),
            budget_effect=(
                "The homogeneous -(partial_z u^z)v can be rewritten as part "
                "of a trace-free strain coefficient, but the radial "
                "commutator remains a separate nonhomogeneous source."
            ),
            support=(
                "axisymmetric divergence-free relation",
                "trace-free strain accounting",
            ),
            missing_evidence=(
                "correlation theorem linking partial_z u^r to partial_r u1",
                "boundary-compatible one-sided strain sign",
            ),
            domination_required=True,
            domination_available=False,
            global_barrier_closed=False,
            clay_navier_stokes_promoted=False,
        ),
        CommutatorBudgetRow(
            row_id="log_biot_savart_strain_hazard",
            gate=GATE,
            term_class="strain_hazard",
            term_or_relation=(
                "partial_z u^r, partial_z u^z, and partial_z psi1 inherit "
                "nonlocal Biot-Savart strain bounds with the restored "
                "coincident-ring logarithmic loss."
            ),
            status="open_log_loss",
            role_at_first_positive_max=(
                "The barrier needs strain coefficients to be controlled at "
                "the same scale where v first crosses; the log loss can "
                "amplify both homogeneous growth and the commutator bound."
            ),
            budget_effect=(
                "A polynomial viscous or local concavity margin is not enough "
                "unless it explicitly absorbs log-amplified strain."
            ),
            support=(
                "Sprint134: NoLogAxisymmetricBiotSavartUniform false",
                "standard axisymmetric Biot-Savart kernel singularity",
            ),
            missing_evidence=(
                "no-log replacement estimate on the active barrier support",
                "log-aware domination inequality",
                "localized cancellation removing the coincident-ring loss",
            ),
            domination_required=True,
            domination_available=False,
            global_barrier_closed=False,
            clay_navier_stokes_promoted=False,
        ),
        CommutatorBudgetRow(
            row_id="domination_hypothesis_pointwise_sign",
            gate=GATE,
            term_class="possible_domination_hypothesis",
            term_or_relation=(
                "-(partial_z u^r) partial_r u1 <= 0 at every possible first "
                "positive maximum of v"
            ),
            status="hypothesis_not_established",
            role_at_first_positive_max=(
                "If true, the nonhomogeneous radial commutator would not help "
                "create the first positive crossing."
            ),
            budget_effect=(
                "This would reduce the local barrier back to homogeneous "
                "strain plus the already tracked 2 u1 partial_z^2 psi1 term."
            ),
            support=(
                "candidate monotone radial profile intuition",
                "local primary-peak geometry only",
            ),
            missing_evidence=(
                "global pointwise sign theorem",
                "secondary-peak compatibility",
                "nonlocal Biot-Savart sign preservation",
            ),
            domination_required=False,
            domination_available=False,
            global_barrier_closed=False,
            clay_navier_stokes_promoted=False,
        ),
        CommutatorBudgetRow(
            row_id="domination_hypothesis_integrated_margin",
            gate=GATE,
            term_class="possible_domination_hypothesis",
            term_or_relation=(
                "|(partial_z u^r) partial_r u1| <= margin from "
                "-2 u1 partial_z^2 psi1, -nu Ltilde v, or an integrated "
                "barrier weight"
            ),
            status="hypothesis_not_established",
            role_at_first_positive_max=(
                "If a scale-uniform margin existed, a positive commutator "
                "burst could be absorbed before it creates a global crossing."
            ),
            budget_effect=(
                "The required estimate must be log-aware, boundary-aware, and "
                "valid at any first-crossing location, not only near the "
                "primary axial maximum."
            ),
            support=(
                "possible weighted maximum-principle route",
                "possible localized Biot-Savart cancellation route",
            ),
            missing_evidence=(
                "explicit margin inequality",
                "constants uniform through the Hou-Luo scaling window",
                "axis and boundary exclusion for the crossing set",
            ),
            domination_required=False,
            domination_available=False,
            global_barrier_closed=False,
            clay_navier_stokes_promoted=False,
        ),
        CommutatorBudgetRow(
            row_id="current_fail_closed_status",
            gate=GATE,
            term_class="decision",
            term_or_relation=(
                "commutator domination open; local barrier not globally "
                "closed; no Clay promotion"
            ),
            status="fail_closed",
            role_at_first_positive_max=(
                "The ledger permits local barrier bookkeeping but refuses to "
                "upgrade it to global axial monotonicity."
            ),
            budget_effect=(
                "Transport commutator domination remains an explicit open "
                "gate for any future Hou-Luo barrier proof."
            ),
            support=(
                "Sprint137 local barrier blockers",
                "Sprint138 commutator budget rows",
            ),
            missing_evidence=(
                "CommutatorDominationForVBarrier",
                "global barrier closure",
                "Clay-level regularity theorem",
            ),
            domination_required=True,
            domination_available=False,
            global_barrier_closed=False,
            clay_navier_stokes_promoted=False,
        ),
    ]
    return [row.as_row() for row in rows]


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = (
        "row_id",
        "gate",
        "term_class",
        "term_or_relation",
        "status",
        "role_at_first_positive_max",
        "budget_effect",
        "support",
        "missing_evidence",
        "domination_required",
        "domination_available",
        "global_barrier_closed",
        "clay_navier_stokes_promoted",
    )
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            serializable = dict(row)
            serializable["support"] = "; ".join(serializable["support"])
            serializable["missing_evidence"] = "; ".join(serializable["missing_evidence"])
            writer.writerow(serializable)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    row_by_id = {row["row_id"]: row for row in rows}
    missing_required = sorted(REQUIRED_ROW_IDS.difference(row_by_id))
    open_hazards = [
        row["row_id"]
        for row in rows
        if row["domination_required"] and not row["domination_available"]
    ]
    hypothesis_rows = [
        row["row_id"]
        for row in rows
        if row["term_class"] == "possible_domination_hypothesis"
    ]

    invariant_failures: list[str] = []
    if missing_required:
        invariant_failures.append("missing_required_rows:" + ",".join(missing_required))
    if "2 v partial_z psi1" not in V_BARRIER_EQUATION:
        invariant_failures.append("homogeneous_2v_partial_z_psi1_missing")
    if "- (partial_z u^z) v" not in V_BARRIER_EQUATION:
        invariant_failures.append("homogeneous_partial_z_uz_v_missing")
    if "- (partial_z u^r) partial_r u1" not in V_BARRIER_EQUATION:
        invariant_failures.append("radial_commutator_missing")
    if row_by_id.get("nonhomogeneous_radial_commutator", {}).get(
        "domination_available"
    ):
        invariant_failures.append("commutator_domination_incorrectly_available")
    if row_by_id.get("incompressibility_relation_limitations", {}).get(
        "domination_available"
    ):
        invariant_failures.append("incompressibility_incorrectly_closes_gate")
    if row_by_id.get("log_biot_savart_strain_hazard", {}).get(
        "domination_available"
    ):
        invariant_failures.append("log_hazard_incorrectly_closed")
    if any(row["global_barrier_closed"] for row in rows):
        invariant_failures.append("global_barrier_incorrectly_closed")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        invariant_failures.append("clay_promotion_detected")
    if not hypothesis_rows:
        invariant_failures.append("no_domination_hypotheses_recorded")

    invariants_passed = not invariant_failures

    return {
        "contract": CONTRACT,
        "gate": GATE,
        "transport_commutator_equation": V_BARRIER_EQUATION,
        "row_count": len(rows),
        "variables": VARIABLES,
        "u1_equation": U1_EQUATION,
        "v_barrier_equation": V_BARRIER_EQUATION,
        "first_positive_maximum": FIRST_POSITIVE_MAX,
        "commutator_decision": COMMUTATOR_DECISION,
        "route_decision": ROUTE_DECISION,
        "fail_closed": True,
        "artifact_complete": invariants_passed,
        "homogeneous_v_terms_classified": True,
        "nonhomogeneous_radial_commutator_classified": True,
        "incompressibility_closes_commutator": False,
        "log_biot_savart_strain_hazard_open": True,
        "possible_domination_hypotheses": hypothesis_rows,
        "commutator_domination_closed": False,
        "commutator_domination_proved": False,
        "commutator_domination_proven": False,
        "local_barrier_globally_closed": False,
        "global_barrier_closed": False,
        "proof_claimed": False,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "promotion_decision": "hold_no_clay_promotion",
        "open_hazards": open_hazards,
        "invariant_failures": invariant_failures,
        "invariants_passed": invariants_passed,
        "exit_code": 0 if invariants_passed else 1,
        "control_card": {
            "O": (
                "Create only the Sprint138 transport commutator emitter and "
                "its output directory surface."
            ),
            "R": (
                "Analyze the v=partial_z u1 barrier equation after Sprint137 "
                "with transport commutator terms made explicit."
            ),
            "C": (
                "Emit deterministic JSON, CSV, and Markdown artifacts with "
                "validate() and main()."
            ),
            "S": (
                "Rows encode homogeneous v terms, the nonhomogeneous radial "
                "commutator, incompressibility limits, log strain hazard, "
                "possible domination hypotheses, and fail-closed status."
            ),
            "L": (
                "The local first-positive-maximum ledger is recorded, but "
                "commutator domination is open and the local barrier is not "
                "globally closed."
            ),
            "P": (
                "Use the artifact as a gate inventory for future Hou-Luo "
                "barrier work, not as a regularity proof."
            ),
            "G": (
                "Validation succeeds only when commutator domination, global "
                "barrier closure, and Clay promotion all remain false."
            ),
            "F": (
                "Missing required rows, missing commutator terms, accidental "
                "domination closure, global proof closure, or Clay promotion "
                "fails validation."
            ),
        },
    }


def validate(summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    row_ids = {row["row_id"] for row in rows}
    missing = REQUIRED_ROW_IDS.difference(row_ids)
    if missing:
        raise ValueError("missing required rows: " + ", ".join(sorted(missing)))
    if summary["contract"] != CONTRACT:
        raise ValueError("wrong contract")
    if summary["gate"] != GATE:
        raise ValueError("wrong gate")
    if summary["commutator_decision"] != COMMUTATOR_DECISION:
        raise ValueError("commutator decision must remain open")
    if summary["route_decision"] != ROUTE_DECISION:
        raise ValueError("route decision must remain fail-closed")
    if summary["commutator_domination_closed"]:
        raise ValueError("commutator domination must remain open")
    if summary["local_barrier_globally_closed"] or summary["global_barrier_closed"]:
        raise ValueError("local barrier must not be reported globally closed")
    if summary["proof_claimed"]:
        raise ValueError("proof must not be claimed")
    if summary["full_clay_ns_solved"] or summary["clay_navier_stokes_promoted"]:
        raise ValueError("Clay promotion is forbidden")
    if not summary["log_biot_savart_strain_hazard_open"]:
        raise ValueError("log Biot-Savart hazard must remain open")
    if "nonhomogeneous_radial_commutator" not in summary["open_hazards"]:
        raise ValueError("nonhomogeneous radial commutator must remain open")
    if summary["incompressibility_closes_commutator"]:
        raise ValueError("incompressibility alone cannot close commutator")
    if summary["invariant_failures"]:
        raise ValueError("; ".join(summary["invariant_failures"]))


def build_report(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 138 Transport Commutator Budget",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Gate: `{summary['gate']}`",
        f"- Commutator decision: `{summary['commutator_decision']}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Commutator domination closed: `{str(summary['commutator_domination_closed']).lower()}`",
        f"- Local barrier globally closed: `{str(summary['local_barrier_globally_closed']).lower()}`",
        f"- Clay Navier-Stokes promoted: `{str(summary['clay_navier_stokes_promoted']).lower()}`",
        "",
        "## Barrier Equation",
        "",
        f"- `{summary['u1_equation']}`",
        f"- `{summary['v_barrier_equation']}`",
        "",
        "## Decision",
        "",
        (
            "Commutator domination is open; the local barrier is not globally "
            "closed; there is no Clay promotion."
        ),
        "",
        "## Rows",
        "",
        "| Row | Status | Class | Term or Relation | Budget Effect |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in rows:
        relation = row["term_or_relation"].replace("|", "\\|")
        effect = row["budget_effect"].replace("|", "\\|")
        lines.append(
            f"| `{row['row_id']}` | `{row['status']}` | `{row['term_class']}` | "
            f"{relation} | {effect} |"
        )
    lines.extend(["", "## Control Card", ""])
    for key, value in summary["control_card"].items():
        lines.append(f"- {key}: {value}")
    return "\n".join(lines) + "\n"


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir if args.out_dir.is_absolute() else repo_root / args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    rows = build_rows()
    summary = build_summary(rows)
    validate(summary, rows)

    write_json(out_dir / ROWS_JSON_NAME, rows)
    write_csv(out_dir / ROWS_CSV_NAME, rows)
    write_json(out_dir / SUMMARY_NAME, summary)
    (out_dir / REPORT_NAME).write_text(build_report(summary, rows), encoding="utf-8")

    print(
        json.dumps(
            {
                "artifact_complete": summary["artifact_complete"],
                "clay_navier_stokes_promoted": summary["clay_navier_stokes_promoted"],
                "commutator_decision": summary["commutator_decision"],
                "commutator_domination_closed": summary["commutator_domination_closed"],
                "contract": summary["contract"],
                "exit_code": summary["exit_code"],
                "global_barrier_closed": summary["global_barrier_closed"],
                "open_hazards": summary["open_hazards"],
                "route_decision": summary["route_decision"],
            },
            sort_keys=True,
        )
    )
    return int(summary["exit_code"])


if __name__ == "__main__":
    sys.exit(main())
