#!/usr/bin/env python3
"""Sprint 138 secondary peak exclusion emitter.

This deterministic emitter analyzes ``SecondaryPeakExclusion`` as the second
Sprint 138 blocker for ``AxialMonotonicityOfSwirlProfile``.

The Sprint 137 gate reduced the axial monotonicity route for
``v = partial_z u1`` to a local parabolic barrier near the primary symmetric
axial peak, while leaving two open blockers: global concavity and secondary
peak exclusion.  This script specializes the secondary-peak blocker.

The decision is intentionally fail-closed: the rows record why a single-peak
initial profile and parabolic smoothing are not enough to exclude later
secondary shoulders or a secondary positive crossing of ``v`` in the coupled
axisymmetric-with-swirl system.  No exclusion theorem is proved here and no
Clay Navier-Stokes promotion is emitted.
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint138_secondary_peak_exclusion"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint138_secondary_peak_exclusion")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_NAME = CONTRACT + "_rows.json"
CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"

GATE = "AxialMonotonicityOfSwirlProfile"
BLOCKER = "SecondaryPeakExclusion"
SPRINT138_BLOCKER_INDEX = 2
ROUTE_DECISION = "fail_closed_blocker_open"

VARIABLES = {
    "u1": "u^theta / r",
    "Gamma": "r u^theta = r^2 u1",
    "v": "partial_z u1",
    "psi1": "psi^theta / r",
    "omega1": "omega^theta / r",
    "Ltilde": "partial_r^2 + (3/r) partial_r + partial_z^2",
    "Dt": "partial_t + u^r partial_r + u^z partial_z",
}

U1_EQUATION = "D_t u1 = 2 u1 partial_z psi1 + nu Ltilde u1"
V_BARRIER_EQUATION = (
    "D_t v = nu Ltilde v + 2 v partial_z psi1 + 2 u1 partial_z^2 psi1 "
    "- (partial_z u^r) partial_r u1 - (partial_z u^z) v"
)
GAMMA_MAXIMUM_PRINCIPLE = (
    "D_t Gamma = nu(Delta - 2 r^-1 partial_r) Gamma, so Gamma has a maximum "
    "principle, but this controls circulation amplitude rather than the "
    "one-dimensional axial peak count of u1 or v."
)

REQUIRED_ROW_IDS = {
    "single_peak_initial_profile",
    "parabolic_smoothing_support",
    "nonlinear_source_can_form_shoulders",
    "annular_gamma_u1_constraints",
    "lack_sturmian_zero_number_principle",
    "possible_secondary_positive_v_crossing",
    "required_exclusion_theorem",
}


@dataclass(frozen=True)
class ExclusionRow:
    row_id: str
    blocker: str
    gate: str
    status: str
    ledger_role: str
    claim_or_observation: str
    support: tuple[str, ...]
    obstruction: tuple[str, ...]
    implication_for_v_barrier: str
    exclusion_proved_here: bool
    blocker_remains_open: bool
    clay_navier_stokes_promoted: bool

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row["support"] = list(self.support)
        row["obstruction"] = list(self.obstruction)
        return row


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def build_rows() -> list[dict[str, Any]]:
    rows = [
        ExclusionRow(
            row_id="single_peak_initial_profile",
            blocker=BLOCKER,
            gate=GATE,
            status="assumption_recorded_not_persistent",
            ledger_role="initial_shape",
            claim_or_observation=(
                "The contemplated Hou-Luo branch may start from a smooth "
                "single primary axial peak for u1 on the monitored half-profile, "
                "with v=partial_z u1 initially nonpositive away from the "
                "symmetry plane."
            ),
            support=(
                "Sprint137 axial monotonicity gate",
                "profile-level single-peak initial data hypothesis",
                "smooth classical data class",
            ),
            obstruction=(
                "initial unimodality is not a time-propagated invariant",
                "the coupled source and transport terms are not scalar heat flow",
            ),
            implication_for_v_barrier=(
                "A first-crossing argument can start from v<=0, but it cannot "
                "exclude a later off-peak local maximum without a persistence "
                "theorem for the single-peak shape."
            ),
            exclusion_proved_here=False,
            blocker_remains_open=True,
            clay_navier_stokes_promoted=False,
        ),
        ExclusionRow(
            row_id="parabolic_smoothing_support",
            blocker=BLOCKER,
            gate=GATE,
            status="support_insufficient",
            ledger_role="regularization",
            claim_or_observation=(
                "Viscosity supplies parabolic smoothing for u1 and v, and at an "
                "interior positive maximum of v the local diffusion contribution "
                "nu Ltilde v is nonpositive."
            ),
            support=(
                "nu Ltilde v maximum-principle sign",
                "classical parabolic smoothing away from coordinate boundary",
                V_BARRIER_EQUATION,
            ),
            obstruction=(
                "smoothing reduces roughness but does not preserve unimodality",
                "the differentiated equation has nonhomogeneous source and "
                "transport-gradient terms",
                "boundary and annular localization can move the first crossing "
                "away from the primary peak",
            ),
            implication_for_v_barrier=(
                "Diffusion cannot by itself create the positive maximum, but "
                "the remaining terms can still invalidate a sign contradiction "
                "at a secondary shoulder."
            ),
            exclusion_proved_here=False,
            blocker_remains_open=True,
            clay_navier_stokes_promoted=False,
        ),
        ExclusionRow(
            row_id="nonlinear_source_can_form_shoulders",
            blocker=BLOCKER,
            gate=GATE,
            status="live_obstruction",
            ledger_role="nonlinear_shoulder_formation",
            claim_or_observation=(
                "The nonlinear source ledger for v contains "
                "2 u1 partial_z^2 psi1 plus coefficients multiplying v and "
                "transport-gradient commutators; this can concentrate growth "
                "off the primary concavity patch."
            ),
            support=(
                U1_EQUATION,
                V_BARRIER_EQUATION,
                "Sprint137 local concavity support only near the primary peak",
            ),
            obstruction=(
                "partial_z^2 psi1 is nonlocal and has no global sign theorem",
                "off-peak positive forcing can raise shoulders before the "
                "primary maximum loses local concavity",
                "no comparison principle orders the coupled source against a "
                "single scalar unimodal envelope",
            ),
            implication_for_v_barrier=(
                "A positive shoulder can become the first positive maximum of "
                "v outside the region where the local source sign is controlled."
            ),
            exclusion_proved_here=False,
            blocker_remains_open=True,
            clay_navier_stokes_promoted=False,
        ),
        ExclusionRow(
            row_id="annular_gamma_u1_constraints",
            blocker=BLOCKER,
            gate=GATE,
            status="constraint_mismatch",
            ledger_role="circulation_vs_swirl_profile",
            claim_or_observation=(
                "The circulation Gamma obeys a maximum-principle type bound, "
                "while u1=Gamma/r^2 is the differentiated axial swirl profile "
                "used in the monotonicity gate."
            ),
            support=(
                GAMMA_MAXIMUM_PRINCIPLE,
                "annular Hou-Luo scaling window away from the axis",
                "bounded circulation amplitude",
            ),
            obstruction=(
                "Gamma control does not control axial zero counts of v",
                "division by r^2 couples annular radial localization to the "
                "effective u1 profile",
                "annular amplitude bounds do not prevent axial shoulders in u1",
            ),
            implication_for_v_barrier=(
                "Gamma/u1 constraints can bound amplitude in the annulus, but "
                "they do not rule out a secondary positive crossing of "
                "partial_z u1."
            ),
            exclusion_proved_here=False,
            blocker_remains_open=True,
            clay_navier_stokes_promoted=False,
        ),
        ExclusionRow(
            row_id="lack_sturmian_zero_number_principle",
            blocker=BLOCKER,
            gate=GATE,
            status="missing_principle",
            ledger_role="zero_number_gap",
            claim_or_observation=(
                "Scalar one-dimensional parabolic equations can sometimes use "
                "a Sturmian zero-number principle to prevent creation of new "
                "sign changes, but the current problem is a coupled "
                "axisymmetric system in (r,z)."
            ),
            support=(
                "v is a derivative of u1 rather than an independent scalar "
                "one-dimensional heat solution",
                "psi1 and velocity gradients are coupled through the "
                "axisymmetric Biot-Savart/elliptic relations",
            ),
            obstruction=(
                "no repo theorem supplies a 1D zero-number monotonicity for "
                "this coupled axisymmetric-with-swirl equation",
                "radial dependence and nonlocal elliptic feedback break the "
                "scalar Sturmian template",
                "source terms can create or move zeros of v",
            ),
            implication_for_v_barrier=(
                "The route cannot infer preservation of the initial single "
                "sign-change pattern of v from known scalar parabolic theory."
            ),
            exclusion_proved_here=False,
            blocker_remains_open=True,
            clay_navier_stokes_promoted=False,
        ),
        ExclusionRow(
            row_id="possible_secondary_positive_v_crossing",
            blocker=BLOCKER,
            gate=GATE,
            status="counter_scenario_open",
            ledger_role="first_crossing_failure_mode",
            claim_or_observation=(
                "A secondary off-peak shoulder may cross into v>0 before any "
                "contradiction is available at the primary symmetric peak."
            ),
            support=(
                "Sprint137 first positive crossing criterion",
                "local primary barrier does not cover the whole half-profile",
                "nonlinear source can act away from the concavity patch",
            ),
            obstruction=(
                "no boundary-free global localization of the first crossing",
                "no exclusion of annular off-peak positive-v maxima",
                "no theorem that the first positive crossing must occur in the "
                "locally concave primary region",
            ),
            implication_for_v_barrier=(
                "This is the exact failure mode for closing "
                "AxialMonotonicityOfSwirlProfile from local barrier support."
            ),
            exclusion_proved_here=False,
            blocker_remains_open=True,
            clay_navier_stokes_promoted=False,
        ),
        ExclusionRow(
            row_id="required_exclusion_theorem",
            blocker=BLOCKER,
            gate=GATE,
            status="required_not_proved",
            ledger_role="theorem_obligation",
            claim_or_observation=(
                "A closing theorem would need to prove that, for the relevant "
                "smooth annular Hou-Luo data class, no secondary axial peak, "
                "shoulder, or positive local maximum of v can form outside the "
                "primary barrier region during the monotonicity time window."
            ),
            support=(
                "required by Sprint137 secondary_peak_blocker",
                "required by Sprint138 blocker index 2",
            ),
            obstruction=(
                "single-peak persistence theorem absent",
                "global sign control for partial_z^2 psi1 absent",
                "coupled axisymmetric zero-number principle absent",
                "annular Gamma/u1 comparison theorem absent",
            ),
            implication_for_v_barrier=(
                "Until this theorem is supplied, the monotonicity gate remains "
                "open and the Hou-Luo symmetric source-sign branch remains "
                "conditional."
            ),
            exclusion_proved_here=False,
            blocker_remains_open=True,
            clay_navier_stokes_promoted=False,
        ),
    ]
    return [row.as_row() for row in rows]


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = (
        "row_id",
        "blocker",
        "gate",
        "status",
        "ledger_role",
        "claim_or_observation",
        "support",
        "obstruction",
        "implication_for_v_barrier",
        "exclusion_proved_here",
        "blocker_remains_open",
        "clay_navier_stokes_promoted",
    )
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            serializable = dict(row)
            serializable["support"] = "; ".join(serializable["support"])
            serializable["obstruction"] = "; ".join(serializable["obstruction"])
            writer.writerow(serializable)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    row_ids = {row["row_id"] for row in rows}
    missing_required = sorted(REQUIRED_ROW_IDS.difference(row_ids))
    open_rows = [row for row in rows if row["blocker_remains_open"]]
    proved_rows = [row for row in rows if row["exclusion_proved_here"]]

    invariant_failures: list[str] = []
    if missing_required:
        invariant_failures.append("missing_required_rows:" + ",".join(missing_required))
    if proved_rows:
        invariant_failures.append(
            "secondary_peak_exclusion_incorrectly_proved:"
            + ",".join(row["row_id"] for row in proved_rows)
        )
    if len(open_rows) != len(rows):
        invariant_failures.append("not_all_rows_keep_blocker_open")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        invariant_failures.append("clay_promotion_detected")
    if not any(row["row_id"] == "nonlinear_source_can_form_shoulders" for row in rows):
        invariant_failures.append("nonlinear_shoulder_row_absent")
    if not any(row["row_id"] == "lack_sturmian_zero_number_principle" for row in rows):
        invariant_failures.append("zero_number_gap_row_absent")
    if not any(row["row_id"] == "annular_gamma_u1_constraints" for row in rows):
        invariant_failures.append("annular_gamma_u1_row_absent")

    invariants_passed = not invariant_failures

    return {
        "contract": CONTRACT,
        "gate": GATE,
        "blocker": BLOCKER,
        "sprint": 138,
        "sprint138_blocker_index": SPRINT138_BLOCKER_INDEX,
        "row_count": len(rows),
        "variables": VARIABLES,
        "u1_equation": U1_EQUATION,
        "v_barrier_equation": V_BARRIER_EQUATION,
        "gamma_maximum_principle": GAMMA_MAXIMUM_PRINCIPLE,
        "route_decision": ROUTE_DECISION,
        "decision": "fail-closed",
        "artifact_complete": invariants_passed,
        "secondary_peak_exclusion_proved": False,
        "secondary_peak_exclusion_status": "not_proved",
        "blocker_remains_open": True,
        "axial_monotonicity_gate_closed": False,
        "axial_monotonicity_gate_status": "open_blocked_by_secondary_peak_exclusion",
        "single_peak_initial_profile_recorded": "single_peak_initial_profile" in row_ids,
        "parabolic_smoothing_support_recorded": "parabolic_smoothing_support" in row_ids,
        "nonlinear_source_can_form_shoulders": (
            "nonlinear_source_can_form_shoulders" in row_ids
        ),
        "annular_gamma_u1_constraints_recorded": "annular_gamma_u1_constraints" in row_ids,
        "sturmian_zero_number_principle_available": False,
        "coupled_axisymmetric_zero_number_gap": True,
        "possible_secondary_positive_v_crossing": (
            "possible_secondary_positive_v_crossing" in row_ids
        ),
        "required_exclusion_theorem_proved": False,
        "clay_navier_stokes_promoted": False,
        "clay_promoted": False,
        "full_clay_ns_solved": False,
        "open_blockers": [BLOCKER],
        "open_row_ids": [row["row_id"] for row in open_rows],
        "invariant_failures": invariant_failures,
        "invariants_passed": invariants_passed,
        "exit_code": 0 if invariants_passed else 1,
        "control_card": {
            "O": (
                "Worker owns only scripts/ns_sprint138_secondary_peak_exclusion.py "
                "and outputs/ns_sprint138_secondary_peak_exclusion/."
            ),
            "R": (
                "Analyze SecondaryPeakExclusion as Sprint138 blocker 2 for "
                "AxialMonotonicityOfSwirlProfile and keep the decision "
                "fail-closed."
            ),
            "C": (
                "Deterministic stdlib Python emitter with dataclass rows, "
                "validate(), main(), JSON, CSV, and Markdown artifacts."
            ),
            "S": (
                "Single-peak initial data and parabolic smoothing are recorded, "
                "but nonlinear source terms, annular Gamma/u1 mismatch, and the "
                "absence of a coupled zero-number theorem leave secondary "
                "positive-v crossings possible."
            ),
            "L": (
                "Sprint137 local barrier support -> secondary shoulder failure "
                "mode -> required exclusion theorem remains absent."
            ),
            "P": (
                "Use this artifact as the fail-closed Sprint138 ledger for the "
                "secondary-peak blocker; do not use it as a proof of axial "
                "monotonicity."
            ),
            "G": (
                "Validation succeeds only when SecondaryPeakExclusion is not "
                "proved, the blocker remains open, and Clay promotion is false."
            ),
            "F": (
                "No Clay promotion; no closed AxialMonotonicityOfSwirlProfile; "
                "no Sturmian 1D zero-number principle is claimed for the "
                "coupled axisymmetric system."
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
    if summary["gate"] != GATE or summary["blocker"] != BLOCKER:
        raise ValueError("wrong gate or blocker")
    if summary["sprint138_blocker_index"] != SPRINT138_BLOCKER_INDEX:
        raise ValueError("wrong Sprint 138 blocker index")
    if summary["route_decision"] != ROUTE_DECISION:
        raise ValueError("route decision must stay fail-closed")
    if summary["secondary_peak_exclusion_proved"]:
        raise ValueError("secondary peak exclusion must remain unproved")
    if summary["required_exclusion_theorem_proved"]:
        raise ValueError("required exclusion theorem must remain unproved")
    if not summary["blocker_remains_open"]:
        raise ValueError("blocker must remain open")
    if summary["axial_monotonicity_gate_closed"]:
        raise ValueError("axial monotonicity gate must remain open")
    if summary["sturmian_zero_number_principle_available"]:
        raise ValueError("Sturmian zero-number principle is not available here")
    if not summary["coupled_axisymmetric_zero_number_gap"]:
        raise ValueError("coupled axisymmetric zero-number gap must be recorded")
    if summary["clay_navier_stokes_promoted"] or summary["full_clay_ns_solved"]:
        raise ValueError("Clay promotion is forbidden")
    if any(row["exclusion_proved_here"] for row in rows):
        raise ValueError("no row may prove secondary peak exclusion")
    if not all(row["blocker_remains_open"] for row in rows):
        raise ValueError("all rows must keep the blocker open")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        raise ValueError("row-level Clay promotion is forbidden")
    if "2 u1 partial_z^2 psi1" not in summary["v_barrier_equation"]:
        raise ValueError("v equation must include the nonlinear source derivative")
    if summary["invariant_failures"]:
        raise ValueError("; ".join(summary["invariant_failures"]))


def build_report(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 138 Secondary Peak Exclusion",
        "",
        f"- Contract: `{CONTRACT}`",
        f"- Gate: `{GATE}`",
        f"- Blocker: `{BLOCKER}`",
        f"- Sprint 138 blocker index: `{summary['sprint138_blocker_index']}`",
        f"- Decision: `{summary['decision']}`",
        (
            "- Secondary peak exclusion proved: "
            f"`{str(summary['secondary_peak_exclusion_proved']).lower()}`"
        ),
        f"- Blocker remains open: `{str(summary['blocker_remains_open']).lower()}`",
        (
            "- Axial monotonicity gate closed: "
            f"`{str(summary['axial_monotonicity_gate_closed']).lower()}`"
        ),
        (
            "- Clay Navier-Stokes promoted: "
            f"`{str(summary['clay_navier_stokes_promoted']).lower()}`"
        ),
        "",
        "## Equations",
        "",
        f"- `{summary['u1_equation']}`",
        f"- `{summary['v_barrier_equation']}`",
        f"- `{summary['gamma_maximum_principle']}`",
        "",
        "## Ledger Rows",
        "",
        "| Row | Status | Role | Observation | Obstruction | Barrier impact |",
        "| --- | --- | --- | --- | --- | --- |",
    ]
    for row in rows:
        observation = row["claim_or_observation"].replace("|", "\\|")
        obstruction = "; ".join(row["obstruction"]).replace("|", "\\|")
        impact = row["implication_for_v_barrier"].replace("|", "\\|")
        lines.append(
            f"| `{row['row_id']}` | `{row['status']}` | `{row['ledger_role']}` | "
            f"{observation} | {obstruction} | {impact} |"
        )
    lines.extend(
        [
            "",
            "## Decision",
            "",
            (
                "SecondaryPeakExclusion is not proved. The second Sprint 138 "
                "blocker remains open for AxialMonotonicityOfSwirlProfile, so "
                "the symmetric Hou-Luo route remains conditional and no Clay "
                "promotion is emitted."
            ),
            "",
            "## Control Card",
            "",
        ]
    )
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

    write_json(out_dir / ROWS_NAME, rows)
    write_csv(out_dir / CSV_NAME, rows)
    write_json(out_dir / SUMMARY_NAME, summary)
    (out_dir / REPORT_NAME).write_text(build_report(summary, rows), encoding="utf-8")

    print(
        json.dumps(
            {
                "artifact_complete": summary["artifact_complete"],
                "blocker": summary["blocker"],
                "blocker_remains_open": summary["blocker_remains_open"],
                "clay_navier_stokes_promoted": summary["clay_navier_stokes_promoted"],
                "contract": summary["contract"],
                "exit_code": summary["exit_code"],
                "gate": summary["gate"],
                "route_decision": summary["route_decision"],
                "secondary_peak_exclusion_proved": summary[
                    "secondary_peak_exclusion_proved"
                ],
            },
            sort_keys=True,
        )
    )
    return int(summary["exit_code"])


if __name__ == "__main__":
    sys.exit(main())
