#!/usr/bin/env python3
"""Sprint 139 pointwise commutator sign-route emitter.

This deterministic artifact records the pointwise sign/dominance route for the
nonhomogeneous transport commutator in the v-barrier,

    -(partial_z u^r) partial_r u1.

It is a route inventory, not a proof.  The emitter separates the cases where a
pointwise sign is known from the cases where the sign is unknown, states the
domination hypotheses that would be needed to absorb the term, preserves the
Biot-Savart logarithmic strain hazard, records radial-gradient coupling, and
keeps the required theorem fail-closed.  No Clay Navier-Stokes promotion is
emitted.
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint139_commutator_sign_route"
GATE = "PointwiseSignDominanceRouteForRadialCommutator"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint139_commutator_sign_route")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"

U1_EQUATION = "D_t u1 = 2 u1 partial_z psi1 + nu Ltilde u1"
V_BARRIER_EQUATION = (
    "D_t v = nu Ltilde v + 2 v partial_z psi1 + 2 u1 partial_z^2 psi1 "
    "- (partial_z u^r) partial_r u1 - (partial_z u^z) v"
)
COMMUTATOR = "-(partial_z u^r) partial_r u1"
FIRST_POSITIVE_MAX = (
    "At a first interior positive maximum of v=partial_z u1, v>0, "
    "partial_r v=partial_z v=0, and Ltilde v<=0."
)
ROUTE_DECISION = "pointwise_sign_route_open_fail_closed"
REQUIRED_THEOREM = "PointwiseRadialCommutatorSignOrDominanceForVBarrier"

REQUIRED_ROW_IDS = {
    "route_inventory",
    "sign_known_favorable_case",
    "sign_unknown_crossing_case",
    "domination_hypothesis_pointwise_margin",
    "domination_hypothesis_weighted_barrier",
    "biot_savart_log_hazard",
    "radial_gradient_coupling",
    "fail_closed_required_theorem",
}


@dataclass(frozen=True)
class SignRouteRow:
    row_id: str
    gate: str
    route_class: str
    local_condition: str
    commutator_effect: str
    status: str
    sign_known: bool
    favorable_if_true: bool
    domination_hypothesis: str
    required_evidence: tuple[str, ...]
    hazards: tuple[str, ...]
    theorem_required: str
    theorem_available: bool
    proof_closed: bool
    clay_navier_stokes_promoted: bool

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row["required_evidence"] = list(self.required_evidence)
        row["hazards"] = list(self.hazards)
        return row


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def build_rows() -> list[dict[str, Any]]:
    rows = [
        SignRouteRow(
            row_id="route_inventory",
            gate=GATE,
            route_class="equation_inventory",
            local_condition=FIRST_POSITIVE_MAX,
            commutator_effect=(
                "The radial commutator is nonhomogeneous in v and can inject "
                "positive forcing at the crossing unless a pointwise sign or "
                "a quantitative dominance margin is supplied."
            ),
            status="encoded_open_gate",
            sign_known=False,
            favorable_if_true=False,
            domination_hypothesis=(
                "Either " + COMMUTATOR + " <= 0 at every admissible first "
                "crossing, or its positive part is absorbed by a log-aware "
                "barrier margin."
            ),
            required_evidence=(
                V_BARRIER_EQUATION,
                "first-crossing maximum-principle geometry",
                "admissible crossing set away from unhandled boundary defects",
            ),
            hazards=(
                "nonhomogeneous source",
                "secondary crossing locations",
                "coincident-ring strain logarithm",
            ),
            theorem_required=REQUIRED_THEOREM,
            theorem_available=False,
            proof_closed=False,
            clay_navier_stokes_promoted=False,
        ),
        SignRouteRow(
            row_id="sign_known_favorable_case",
            gate=GATE,
            route_class="sign_known",
            local_condition=(
                "Assume sign(partial_z u^r) agrees with sign(partial_r u1) "
                "so that " + COMMUTATOR + " <= 0 at the crossing."
            ),
            commutator_effect=(
                "Under this conditional sign, the radial commutator cannot "
                "create the first positive v crossing."
            ),
            status="conditional_route_only",
            sign_known=True,
            favorable_if_true=True,
            domination_hypothesis="pointwise favorable sign at all possible crossings",
            required_evidence=(
                "global pointwise sign theorem for partial_z u^r partial_r u1",
                "compatibility with secondary peaks and off-axis crossings",
                "persistence through the Hou-Luo scaling window",
            ),
            hazards=(
                "known only as a hypothetical branch",
                "no Biot-Savart sign preservation theorem recorded",
            ),
            theorem_required=REQUIRED_THEOREM,
            theorem_available=False,
            proof_closed=False,
            clay_navier_stokes_promoted=False,
        ),
        SignRouteRow(
            row_id="sign_unknown_crossing_case",
            gate=GATE,
            route_class="sign_unknown",
            local_condition=(
                "No theorem fixes the correlation between partial_z u^r and "
                "partial_r u1 at an arbitrary first positive maximum of v."
            ),
            commutator_effect=(
                "The positive part max(" + COMMUTATOR + ", 0) remains an "
                "uncontrolled source in the pointwise barrier inequality."
            ),
            status="live_obstruction",
            sign_known=False,
            favorable_if_true=False,
            domination_hypothesis=(
                "positive part must be bounded by a favorable local or "
                "weighted margin before the first crossing"
            ),
            required_evidence=(
                "correlation estimate for partial_z u^r and partial_r u1",
                "uniform treatment of primary and secondary maxima",
                "boundary and axis compatibility",
            ),
            hazards=(
                "sign reversal",
                "off-peak shoulder formation",
                "nonlocal strain coupling",
            ),
            theorem_required=REQUIRED_THEOREM,
            theorem_available=False,
            proof_closed=False,
            clay_navier_stokes_promoted=False,
        ),
        SignRouteRow(
            row_id="domination_hypothesis_pointwise_margin",
            gate=GATE,
            route_class="domination_hypothesis",
            local_condition=(
                "At every first positive maximum, max(" + COMMUTATOR + ", 0) "
                "<= M_point, where M_point is supplied by favorable "
                "concavity, diffusion, or source sign."
            ),
            commutator_effect=(
                "A strict pointwise margin would absorb positive commutator "
                "bursts before v crosses above zero."
            ),
            status="hypothesis_required_not_proved",
            sign_known=False,
            favorable_if_true=True,
            domination_hypothesis=(
                "max(" + COMMUTATOR + ", 0) <= "
                "[-nu Ltilde v - 2 u1 partial_z^2 psi1 - admissible strain*v]_+"
            ),
            required_evidence=(
                "explicit nonnegative margin with constants",
                "scale-uniform estimates in the active barrier window",
                "proof that the margin is available at every crossing point",
            ),
            hazards=(
                "diffusion has the wrong sign at a positive maximum after moving terms",
                "partial_z^2 psi1 is nonlocal and sign-indefinite",
                "strain coefficients may carry logarithmic loss",
            ),
            theorem_required=REQUIRED_THEOREM,
            theorem_available=False,
            proof_closed=False,
            clay_navier_stokes_promoted=False,
        ),
        SignRouteRow(
            row_id="domination_hypothesis_weighted_barrier",
            gate=GATE,
            route_class="domination_hypothesis",
            local_condition=(
                "Use a weighted barrier B=w(r,z,t)v and require the positive "
                "commutator source to be absorbed by weight-generated drift, "
                "diffusion, and source margins."
            ),
            commutator_effect=(
                "A successful weight could trade pointwise sign for a "
                "quantitative dominance inequality over the crossing set."
            ),
            status="hypothesis_required_not_proved",
            sign_known=False,
            favorable_if_true=True,
            domination_hypothesis=(
                "w max(" + COMMUTATOR + ", 0) is dominated by the full "
                "weighted maximum-principle budget without hidden positive "
                "remainders"
            ),
            required_evidence=(
                "constructive weight with controlled derivatives",
                "no boundary leakage from the weighted operator",
                "log-aware constants for Biot-Savart strain terms",
            ),
            hazards=(
                "weight derivatives create new commutators",
                "radial boundary and axis terms may leak",
                "secondary maxima may move outside the designed weight window",
            ),
            theorem_required=REQUIRED_THEOREM,
            theorem_available=False,
            proof_closed=False,
            clay_navier_stokes_promoted=False,
        ),
        SignRouteRow(
            row_id="biot_savart_log_hazard",
            gate=GATE,
            route_class="biot_savart_log_hazard",
            local_condition=(
                "partial_z u^r is recovered nonlocally from the axisymmetric "
                "Biot-Savart law and may inherit the coincident-ring "
                "logarithmic strain loss."
            ),
            commutator_effect=(
                "Even if partial_r u1 is locally bounded, a log-amplified "
                "partial_z u^r estimate can exceed a polynomial pointwise "
                "margin."
            ),
            status="open_hazard",
            sign_known=False,
            favorable_if_true=False,
            domination_hypothesis=(
                "any dominance theorem must absorb or cancel the Biot-Savart "
                "log factor on the active crossing scale"
            ),
            required_evidence=(
                "localized no-log replacement estimate, or",
                "log-aware commutator dominance inequality, or",
                "structural cancellation of the coincident-ring contribution",
            ),
            hazards=(
                "restored Biot-Savart logarithm",
                "strain coefficient time-integrability gap",
                "nonlocal sign is not preserved by the kernel",
            ),
            theorem_required=REQUIRED_THEOREM,
            theorem_available=False,
            proof_closed=False,
            clay_navier_stokes_promoted=False,
        ),
        SignRouteRow(
            row_id="radial_gradient_coupling",
            gate=GATE,
            route_class="radial_gradient_coupling",
            local_condition=(
                "The factor partial_r u1 is not fixed by the axial condition "
                "v=partial_z u1 at the first positive maximum."
            ),
            commutator_effect=(
                "Radial steepening of u1 can amplify the commutator "
                "independently of the axial monotonicity variable v."
            ),
            status="coupling_open",
            sign_known=False,
            favorable_if_true=False,
            domination_hypothesis=(
                "partial_r u1 must be controlled by the same barrier ledger "
                "or by an independent radial monotonicity/regularity theorem"
            ),
            required_evidence=(
                "radial-gradient bound at first axial crossing",
                "coupled equation control for partial_r u1",
                "compatibility with viscosity, axis behavior, and boundary data",
            ),
            hazards=(
                "radial gradient can peak where v is just crossing",
                "radial and axial monotonicity are not interchangeable",
                "incompressibility does not determine partial_r u1",
            ),
            theorem_required=REQUIRED_THEOREM,
            theorem_available=False,
            proof_closed=False,
            clay_navier_stokes_promoted=False,
        ),
        SignRouteRow(
            row_id="fail_closed_required_theorem",
            gate=GATE,
            route_class="required_theorem",
            local_condition=(
                REQUIRED_THEOREM
                + " must prove either favorable sign or quantitative "
                "dominance for " + COMMUTATOR + " on every admissible "
                "first-crossing configuration."
            ),
            commutator_effect=(
                "Until that theorem is supplied, the pointwise sign route "
                "does not close the v-barrier."
            ),
            status="fail_closed",
            sign_known=False,
            favorable_if_true=False,
            domination_hypothesis=(
                "the required theorem is named but unavailable; no proof "
                "closure is emitted"
            ),
            required_evidence=(
                "complete pointwise sign theorem, or",
                "complete log-aware dominance theorem,",
                "formal integration into the global axial monotonicity barrier",
            ),
            hazards=(
                "accidental proof promotion",
                "Clay-level overclaim",
                "omitted sign-unknown crossing case",
            ),
            theorem_required=REQUIRED_THEOREM,
            theorem_available=False,
            proof_closed=False,
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
        "route_class",
        "local_condition",
        "commutator_effect",
        "status",
        "sign_known",
        "favorable_if_true",
        "domination_hypothesis",
        "required_evidence",
        "hazards",
        "theorem_required",
        "theorem_available",
        "proof_closed",
        "clay_navier_stokes_promoted",
    )
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            serializable = dict(row)
            serializable["required_evidence"] = "; ".join(serializable["required_evidence"])
            serializable["hazards"] = "; ".join(serializable["hazards"])
            writer.writerow(serializable)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    row_by_id = {row["row_id"]: row for row in rows}
    missing_required = sorted(REQUIRED_ROW_IDS.difference(row_by_id))
    open_rows = [
        row["row_id"]
        for row in rows
        if not row["theorem_available"] or not row["proof_closed"]
    ]
    domination_rows = [
        row["row_id"]
        for row in rows
        if row["route_class"] == "domination_hypothesis"
    ]

    invariant_failures: list[str] = []
    if missing_required:
        invariant_failures.append("missing_required_rows:" + ",".join(missing_required))
    for required_text in (
        "sign_known",
        "sign_unknown",
        "domination_hypothesis",
        "biot_savart_log_hazard",
        "radial_gradient_coupling",
        "required_theorem",
    ):
        if not any(row["route_class"] == required_text for row in rows):
            invariant_failures.append("missing_route_class:" + required_text)
    if "(partial_z u^r) partial_r u1" not in V_BARRIER_EQUATION:
        invariant_failures.append("commutator_missing_from_barrier_equation")
    if not domination_rows:
        invariant_failures.append("no_domination_hypotheses")
    if row_by_id.get("sign_known_favorable_case", {}).get("theorem_available"):
        invariant_failures.append("conditional_sign_incorrectly_promoted")
    if row_by_id.get("sign_unknown_crossing_case", {}).get("proof_closed"):
        invariant_failures.append("sign_unknown_case_incorrectly_closed")
    if row_by_id.get("biot_savart_log_hazard", {}).get("theorem_available"):
        invariant_failures.append("biot_savart_log_hazard_incorrectly_closed")
    if row_by_id.get("radial_gradient_coupling", {}).get("theorem_available"):
        invariant_failures.append("radial_gradient_coupling_incorrectly_closed")
    if any(row["proof_closed"] for row in rows):
        invariant_failures.append("proof_closure_detected")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        invariant_failures.append("clay_promotion_detected")

    invariants_passed = not invariant_failures

    return {
        "contract": CONTRACT,
        "gate": GATE,
        "required_theorem": REQUIRED_THEOREM,
        "row_count": len(rows),
        "u1_equation": U1_EQUATION,
        "v_barrier_equation": V_BARRIER_EQUATION,
        "commutator": COMMUTATOR,
        "first_positive_maximum": FIRST_POSITIVE_MAX,
        "route_decision": ROUTE_DECISION,
        "artifact_complete": invariants_passed,
        "fail_closed": True,
        "sign_known_route_recorded": True,
        "sign_unknown_route_recorded": True,
        "domination_hypotheses_recorded": domination_rows,
        "biot_savart_log_hazard_open": True,
        "radial_gradient_coupling_open": True,
        "required_theorem_available": False,
        "required_theorem_closed": False,
        "commutator_sign_route_closed": False,
        "commutator_domination_closed": False,
        "commutator_domination_proved": False,
        "commutator_domination_proven": False,
        "global_barrier_closed": False,
        "proof_claimed": False,
        "proof_closed": False,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "promotion_decision": "hold_no_clay_promotion",
        "open_rows": open_rows,
        "invariant_failures": invariant_failures,
        "invariants_passed": invariants_passed,
        "exit_code": 0 if invariants_passed else 1,
        "control_card": {
            "O": (
                "Worker owns only scripts/ns_sprint139_commutator_sign_route.py "
                "and outputs/ns_sprint139_commutator_sign_route/."
            ),
            "R": (
                "Record the pointwise sign/dominance route for "
                + COMMUTATOR
                + " in the v-barrier."
            ),
            "C": (
                "Emit deterministic JSON, CSV, and Markdown artifacts with "
                "fail-closed validation."
            ),
            "S": (
                "Rows cover sign-known, sign-unknown, domination hypotheses, "
                "Biot-Savart log hazard, radial-gradient coupling, and the "
                "required theorem."
            ),
            "L": (
                "The route inventory is complete, but the sign/dominance "
                "theorem is unavailable and the v-barrier is not closed."
            ),
            "P": (
                "Use this as a Sprint 139 route ledger for future barrier "
                "work, not as a regularity proof."
            ),
            "G": (
                "Validation succeeds only when proof closure, theorem "
                "availability, commutator domination, and Clay promotion all "
                "remain false."
            ),
            "F": (
                "Missing required rows, closed sign-unknown case, hidden "
                "log-hazard closure, proof closure, or Clay promotion fails "
                "validation."
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
    if summary["route_decision"] != ROUTE_DECISION:
        raise ValueError("route must remain open and fail-closed")
    if summary["required_theorem_available"] or summary["required_theorem_closed"]:
        raise ValueError("required theorem must remain unavailable")
    if summary["commutator_sign_route_closed"] or summary["commutator_domination_closed"]:
        raise ValueError("commutator sign/domination route must remain open")
    if summary["proof_claimed"] or summary["proof_closed"]:
        raise ValueError("proof closure is forbidden")
    if summary["full_clay_ns_solved"] or summary["clay_navier_stokes_promoted"]:
        raise ValueError("Clay promotion is forbidden")
    if not summary["biot_savart_log_hazard_open"]:
        raise ValueError("Biot-Savart log hazard must remain open")
    if not summary["radial_gradient_coupling_open"]:
        raise ValueError("radial-gradient coupling must remain open")
    if "sign_unknown_crossing_case" not in summary["open_rows"]:
        raise ValueError("sign-unknown crossing case must remain open")
    if "fail_closed_required_theorem" not in summary["open_rows"]:
        raise ValueError("required theorem row must remain open")
    if summary["invariant_failures"]:
        raise ValueError("; ".join(summary["invariant_failures"]))


def build_report(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 139 Commutator Sign Route",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Gate: `{summary['gate']}`",
        f"- Required theorem: `{summary['required_theorem']}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Commutator sign route closed: `{str(summary['commutator_sign_route_closed']).lower()}`",
        f"- Commutator domination closed: `{str(summary['commutator_domination_closed']).lower()}`",
        f"- Proof closed: `{str(summary['proof_closed']).lower()}`",
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
            "The pointwise sign/dominance route is recorded but remains open. "
            "The required theorem is unavailable, the proof is not closed, "
            "and no Clay promotion is emitted."
        ),
        "",
        "## Rows",
        "",
        "| Row | Status | Class | Local Condition | Commutator Effect |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in rows:
        condition = row["local_condition"].replace("|", "\\|")
        effect = row["commutator_effect"].replace("|", "\\|")
        lines.append(
            f"| `{row['row_id']}` | `{row['status']}` | `{row['route_class']}` | "
            f"{condition} | {effect} |"
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
                "commutator_domination_closed": summary["commutator_domination_closed"],
                "commutator_sign_route_closed": summary["commutator_sign_route_closed"],
                "contract": summary["contract"],
                "exit_code": summary["exit_code"],
                "proof_closed": summary["proof_closed"],
                "required_theorem_available": summary["required_theorem_available"],
                "route_decision": summary["route_decision"],
            },
            sort_keys=True,
        )
    )
    return int(summary["exit_code"])


if __name__ == "__main__":
    sys.exit(main())
