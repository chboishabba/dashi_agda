#!/usr/bin/env python3
"""Sprint 141 commutator domination inequality ledger.

This deterministic stdlib emitter normalizes the budget needed to dominate
the positive nonhomogeneous term

    max(-(partial_z u^r) partial_r u1, 0)

in the barrier equation for v = partial_z u1.  It records the favorable
concavity margin, diffusion/homogeneous strain terms, the commutator positive
part, the logarithmic Biot-Savart loss, and the missing simultaneous
inequality.  The artifact is a fail-closed ledger: it emits no theorem, no
global barrier, and no Clay Navier-Stokes promotion.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint141_commutator_domination_inequality"
GATE = "CommutatorDominationInequalityForVBarrier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint141_commutator_domination_inequality")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"

SPRINT = 141
AFTER_SPRINT = 140
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
VARIABLE = "v = partial_z u1"
POSITIVE_COMMUTATOR = "max(-(partial_z u^r) partial_r u1, 0)"
U1_EQUATION = "D_t u1 = 2 u1 partial_z psi1 + nu Ltilde u1"
V_BARRIER_EQUATION = (
    "D_t v = nu Ltilde v + 2 v partial_z psi1 + 2 u1 partial_z^2 psi1 "
    "- (partial_z u^r) partial_r u1 - (partial_z u^z) v"
)
NORMALIZED_TARGET_INEQUALITY = (
    "C_comm * Log_BS(active_scale) * |partial_r u1| <= "
    "kappa_concavity + kappa_diffusion - C_strain - slack"
)
ROUTE_DECISION = "fail_closed_missing_simultaneous_domination_inequality"
PROMOTION_DECISION = "hold_no_clay_promotion"
REQUIRED_THEOREM = "SimultaneousLogAwareCommutatorDominationForVBarrier"

FAVORABLE_CONCAVITY = "favorable_concavity_margin"
DIFFUSION_HOMOGENEOUS_STRAIN = "diffusion_homogeneous_strain"
COMMUTATOR_POSITIVE_PART = "commutator_positive_part"
LOG_BIOT_SAVART_LOSS = "log_biot_savart_loss"
MISSING_SIMULTANEOUS_INEQUALITY = "missing_simultaneous_inequality"

REQUIRED_ROW_IDS = {
    FAVORABLE_CONCAVITY,
    DIFFUSION_HOMOGENEOUS_STRAIN,
    COMMUTATOR_POSITIVE_PART,
    LOG_BIOT_SAVART_LOSS,
    MISSING_SIMULTANEOUS_INEQUALITY,
}


@dataclass(frozen=True)
class InequalityRow:
    row_id: str
    ledger_role: str
    normalized_symbol: str
    sign_in_budget: str
    term_or_margin: str
    normalized_budget_entry: str
    required_bound: str
    available_evidence: tuple[str, ...]
    missing_evidence: tuple[str, ...]
    inequality_status: str
    contributes_favorable_margin: bool
    contributes_adverse_load: bool
    log_loss_present: bool
    simultaneous_required: bool
    theorem_available: bool
    theorem_proved: bool
    proof_closed: bool
    global_barrier_closed: bool
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row["available_evidence"] = list(self.available_evidence)
        row["missing_evidence"] = list(self.missing_evidence)
        row["hazard_id"] = self.row_id if self.contributes_adverse_load else ""
        row["hazard_name"] = (
            "commutator_budget_hazard"
            if self.contributes_adverse_load
            else "not_a_hazard_row"
        )
        row["constants_absent"] = True
        row["log_aware_theorem_absent"] = True
        row["missing_log_aware_theorem"] = REQUIRED_THEOREM
        row["claim_closed"] = self.proof_closed
        row["claim_proved"] = self.theorem_proved
        row["claim_proven"] = self.theorem_proved
        row["row_hash"] = stable_hash({k: v for k, v in row.items() if k != "row_hash"})
        return row


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def stable_hash(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def build_rows() -> list[dict[str, Any]]:
    rows = [
        InequalityRow(
            row_id=FAVORABLE_CONCAVITY,
            ledger_role="favorable_margin",
            normalized_symbol="kappa_concavity",
            sign_in_budget="favorable_if_positive",
            term_or_margin="-2 u1 partial_z^2 psi1 after moving favorable concavity to the margin side",
            normalized_budget_entry="available_margin += kappa_concavity(active_crossing_set)",
            required_bound=(
                "kappa_concavity > 0 on every admissible first positive "
                "maximum of v, with the same scale and window as the "
                "commutator estimate"
            ),
            available_evidence=(
                "Sprint 138/140 ledgers identify concavity as a candidate favorable source margin",
                "local primary-profile heuristic is recorded as conditional evidence",
            ),
            missing_evidence=(
                "global concavity theorem for partial_z^2 psi1 on all crossing points",
                "scale-uniform lower constant kappa_concavity",
                "compatibility with secondary peaks, axis behavior, and boundary leakage",
            ),
            inequality_status="margin_required_not_available",
            contributes_favorable_margin=True,
            contributes_adverse_load=False,
            log_loss_present=False,
            simultaneous_required=True,
            theorem_available=False,
            theorem_proved=False,
            proof_closed=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        InequalityRow(
            row_id=DIFFUSION_HOMOGENEOUS_STRAIN,
            ledger_role="diffusion_and_homogeneous_strain_budget",
            normalized_symbol="kappa_diffusion_minus_C_strain",
            sign_in_budget="mixed",
            term_or_margin="nu Ltilde v + 2 v partial_z psi1 - (partial_z u^z) v",
            normalized_budget_entry=(
                "available_margin += kappa_diffusion; adverse_load += "
                "C_strain * v_max"
            ),
            required_bound=(
                "diffusion and homogeneous strain must leave a nonnegative "
                "residual margin after time integration and any log-amplified "
                "strain coefficient"
            ),
            available_evidence=(
                "first-positive-maximum geometry gives Ltilde v <= 0",
                "homogeneous v terms are identified as linear in v at the crossing",
            ),
            missing_evidence=(
                "strict usable diffusion margin at the crossing",
                "time-integrable bound for partial_z psi1 and partial_z u^z with log loss included",
                "residual margin after combining diffusion, strain, concavity, and commutator terms",
            ),
            inequality_status="budget_required_not_closed",
            contributes_favorable_margin=True,
            contributes_adverse_load=True,
            log_loss_present=True,
            simultaneous_required=True,
            theorem_available=False,
            theorem_proved=False,
            proof_closed=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        InequalityRow(
            row_id=COMMUTATOR_POSITIVE_PART,
            ledger_role="positive_nonhomogeneous_load",
            normalized_symbol="C_comm",
            sign_in_budget="adverse_positive_part",
            term_or_margin=POSITIVE_COMMUTATOR,
            normalized_budget_entry="adverse_load += max(-(partial_z u^r) partial_r u1, 0)",
            required_bound=(
                "max(-(partial_z u^r) partial_r u1, 0) must be bounded by "
                "the favorable residual margin at every admissible first "
                "positive maximum of v"
            ),
            available_evidence=(
                "Sprint 138 isolates the radial commutator as nonhomogeneous in v",
                "Sprint 139 records sign and domination routes as hypotheses",
            ),
            missing_evidence=(
                "pointwise favorable sign theorem",
                "radial-gradient control for partial_r u1 on the active crossing set",
                "quantitative domination constant compatible with concavity and diffusion",
            ),
            inequality_status="positive_part_uncontrolled",
            contributes_favorable_margin=False,
            contributes_adverse_load=True,
            log_loss_present=False,
            simultaneous_required=True,
            theorem_available=False,
            theorem_proved=False,
            proof_closed=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        InequalityRow(
            row_id=LOG_BIOT_SAVART_LOSS,
            ledger_role="nonlocal_logarithmic_loss",
            normalized_symbol="Log_BS(active_scale)",
            sign_in_budget="adverse_multiplier",
            term_or_margin="partial_z u^r recovered through axisymmetric Biot-Savart strain",
            normalized_budget_entry=(
                "adverse_load += C_comm * Log_BS(active_scale) * |partial_r u1|"
            ),
            required_bound=(
                "the commutator estimate must either absorb the restored "
                "coincident-ring logarithm or prove a structural cancellation "
                "removing it on the active support"
            ),
            available_evidence=(
                "Sprint 134 records the uniform no-log axisymmetric Biot-Savart estimate as false",
                "Sprint 138/139 keep log-aware commutator domination open",
            ),
            missing_evidence=(
                "localized no-log replacement estimate",
                "log-aware dominance inequality with explicit constants",
                "kernel cancellation theorem at the crossing scale",
            ),
            inequality_status="log_loss_open",
            contributes_favorable_margin=False,
            contributes_adverse_load=True,
            log_loss_present=True,
            simultaneous_required=True,
            theorem_available=False,
            theorem_proved=False,
            proof_closed=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        InequalityRow(
            row_id=MISSING_SIMULTANEOUS_INEQUALITY,
            ledger_role="simultaneous_closure_gate",
            normalized_symbol="Delta = kappa_concavity + kappa_diffusion - C_strain - C_comm * Log_BS * |partial_r u1|",
            sign_in_budget="must_be_strictly_positive",
            term_or_margin=NORMALIZED_TARGET_INEQUALITY,
            normalized_budget_entry="require Delta >= slack > 0 on one common crossing set",
            required_bound=(
                "there must be one simultaneous inequality using the same "
                "crossing set, scale, time window, constants, and boundary "
                "conditions for concavity, diffusion, strain, commutator, and "
                "Biot-Savart log loss"
            ),
            available_evidence=(
                "all required ledger components have been named",
                "the normalized inequality target is explicit",
            ),
            missing_evidence=(
                REQUIRED_THEOREM,
                "single active crossing-set theorem shared by every row",
                "strict positive slack after all adverse loads and log losses",
                "global barrier theorem separated from local conditional bookkeeping",
            ),
            inequality_status="missing_required_theorem_fail_closed",
            contributes_favorable_margin=False,
            contributes_adverse_load=False,
            log_loss_present=True,
            simultaneous_required=True,
            theorem_available=False,
            theorem_proved=False,
            proof_closed=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
    ]
    return [row.as_row() for row in rows]


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = (
        "row_id",
        "ledger_role",
        "normalized_symbol",
        "sign_in_budget",
        "term_or_margin",
        "normalized_budget_entry",
        "required_bound",
        "available_evidence",
        "missing_evidence",
        "hazard_id",
        "hazard_name",
        "constants_absent",
        "log_aware_theorem_absent",
        "missing_log_aware_theorem",
        "inequality_status",
        "contributes_favorable_margin",
        "contributes_adverse_load",
        "log_loss_present",
        "simultaneous_required",
        "theorem_available",
        "theorem_proved",
        "proof_closed",
        "global_barrier_closed",
        "full_clay_ns_solved",
        "clay_navier_stokes_promoted",
        "claim_closed",
        "claim_proved",
        "claim_proven",
        "row_hash",
    )
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            serializable = dict(row)
            serializable["available_evidence"] = "; ".join(serializable["available_evidence"])
            serializable["missing_evidence"] = "; ".join(serializable["missing_evidence"])
            writer.writerow(serializable)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    row_by_id = {row["row_id"]: row for row in rows}
    missing_required = sorted(REQUIRED_ROW_IDS.difference(row_by_id))
    row_hashes = {row["row_id"]: row["row_hash"] for row in rows}
    rows_hash = stable_hash(rows)

    favorable_rows = [
        row["row_id"] for row in rows if row["contributes_favorable_margin"]
    ]
    adverse_rows = [row["row_id"] for row in rows if row["contributes_adverse_load"]]
    open_rows = [
        row["row_id"]
        for row in rows
        if not row["theorem_available"] or not row["proof_closed"]
    ]

    invariant_failures: list[str] = []
    if missing_required:
        invariant_failures.append("missing_required_rows:" + ",".join(missing_required))
    if not row_by_id.get(FAVORABLE_CONCAVITY, {}).get("contributes_favorable_margin"):
        invariant_failures.append("favorable_concavity_margin_not_favorable")
    if not row_by_id.get(DIFFUSION_HOMOGENEOUS_STRAIN, {}).get(
        "contributes_adverse_load"
    ):
        invariant_failures.append("diffusion_homogeneous_strain_mixed_budget_missing")
    if not row_by_id.get(COMMUTATOR_POSITIVE_PART, {}).get("contributes_adverse_load"):
        invariant_failures.append("commutator_positive_part_not_adverse")
    if not row_by_id.get(LOG_BIOT_SAVART_LOSS, {}).get("log_loss_present"):
        invariant_failures.append("log_biot_savart_loss_not_present")
    if REQUIRED_THEOREM not in row_by_id.get(MISSING_SIMULTANEOUS_INEQUALITY, {}).get(
        "missing_evidence", []
    ):
        invariant_failures.append("missing_simultaneous_theorem_not_recorded")
    if any(row["theorem_available"] for row in rows):
        invariant_failures.append("theorem_incorrectly_available")
    if any(row["theorem_proved"] for row in rows):
        invariant_failures.append("theorem_incorrectly_proved")
    if any(row["proof_closed"] for row in rows):
        invariant_failures.append("proof_closure_detected")
    if any(row["global_barrier_closed"] for row in rows):
        invariant_failures.append("global_barrier_closure_detected")
    if any(row["full_clay_ns_solved"] for row in rows):
        invariant_failures.append("full_clay_ns_solved_detected")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        invariant_failures.append("clay_promotion_detected")
    if not all(row["simultaneous_required"] for row in rows):
        invariant_failures.append("non_simultaneous_row_detected")

    invariants_passed = not invariant_failures
    return {
        "contract": CONTRACT,
        "gate": GATE,
        "sprint": SPRINT,
        "after_sprint": AFTER_SPRINT,
        "program": PROGRAM,
        "variable": VARIABLE,
        "row_count": len(rows),
        "required_row_ids": sorted(REQUIRED_ROW_IDS),
        "u1_equation": U1_EQUATION,
        "v_barrier_equation": V_BARRIER_EQUATION,
        "positive_nonhomogeneous_term": POSITIVE_COMMUTATOR,
        "normalized_target_inequality": NORMALIZED_TARGET_INEQUALITY,
        "required_theorem": REQUIRED_THEOREM,
        "required_theorem_available": False,
        "required_theorem_proved": False,
        "required_theorem_proven": False,
        "required_theorem_closed": False,
        "constants_absent": True,
        "constant_compatibility_absent": True,
        "log_aware_theorem_absent": True,
        "log_aware_commutator_theorem_absent": True,
        "missing_log_aware_theorem": REQUIRED_THEOREM,
        "route_decision": ROUTE_DECISION,
        "promotion_decision": PROMOTION_DECISION,
        "artifact_complete": invariants_passed,
        "fail_closed": True,
        "favorable_margin_rows": favorable_rows,
        "adverse_load_rows": adverse_rows,
        "open_rows": open_rows,
        "commutator_positive_part_controlled": False,
        "commutator_domination_closed": False,
        "commutator_domination_proved": False,
        "commutator_domination_proven": False,
        "log_biot_savart_loss_absorbed": False,
        "simultaneous_inequality_available": False,
        "simultaneous_inequality_proved": False,
        "local_barrier_globally_closed": False,
        "global_barrier": False,
        "global_barrier_closed": False,
        "global_proof": False,
        "global_proof_closed": False,
        "unconditional_proof": False,
        "proved_theorem": False,
        "proof_claimed": False,
        "proof_closed": False,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "clay_promoted": False,
        "row_hashes": row_hashes,
        "rows_hash": rows_hash,
        "summary_payload_hash_without_self": stable_hash(
            {
                "contract": CONTRACT,
                "required_row_ids": sorted(REQUIRED_ROW_IDS),
                "normalized_target_inequality": NORMALIZED_TARGET_INEQUALITY,
                "row_hashes": row_hashes,
                "rows_hash": rows_hash,
            }
        ),
        "invariant_failures": invariant_failures,
        "invariants_passed": invariants_passed,
        "exit_code": 0 if invariants_passed else 1,
        "control_card": {
            "O": (
                "Sprint 141 lane 2 owns only "
                "scripts/ns_sprint141_commutator_domination_inequality.py and "
                "outputs/ns_sprint141_commutator_domination_inequality/."
            ),
            "R": (
                "Derive a normalized inequality/budget ledger for "
                "max(-(partial_z u^r) partial_r u1, 0) in the "
                "v=partial_z u1 barrier equation."
            ),
            "C": (
                "Stdlib deterministic emitter producing JSON summary, JSON "
                "rows, CSV, and Markdown with stable hashes."
            ),
            "S": (
                "Rows cover favorable concavity margin, diffusion/homogeneous "
                "strain, commutator positive part, log Biot-Savart loss, and "
                "the missing simultaneous inequality."
            ),
            "L": (
                "The ledger normalizes the required inequality but records no "
                "available simultaneous theorem, no closed domination, and no "
                "global barrier."
            ),
            "P": (
                "Use this as the next analytic obligation ledger before any "
                "barrier or promotion attempt."
            ),
            "G": (
                "Validation succeeds only while proved theorem, global "
                "barrier, full_clay_ns_solved, and "
                "clay_navier_stokes_promoted are all false."
            ),
            "F": (
                "Missing required rows, absent log-loss accounting, accidental "
                "theorem/proof closure, global barrier closure, or Clay "
                "promotion fails validation."
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
        raise ValueError("route decision must remain fail-closed")
    if summary["required_theorem_available"] or summary["required_theorem_closed"]:
        raise ValueError("required theorem must remain unavailable")
    if summary["proved_theorem"] or summary["proof_claimed"] or summary["proof_closed"]:
        raise ValueError("proved theorem/proof closure is forbidden")
    if summary["global_barrier"] or summary["global_barrier_closed"]:
        raise ValueError("global barrier closure is forbidden")
    if summary["local_barrier_globally_closed"]:
        raise ValueError("local barrier must not be reported globally closed")
    if summary["full_clay_ns_solved"] or summary["clay_navier_stokes_promoted"]:
        raise ValueError("Clay promotion is forbidden")
    if summary["commutator_domination_closed"]:
        raise ValueError("commutator domination must remain open")
    if summary["commutator_positive_part_controlled"]:
        raise ValueError("positive commutator must remain uncontrolled")
    if summary["log_biot_savart_loss_absorbed"]:
        raise ValueError("log Biot-Savart loss must remain unabsorbed")
    if summary["simultaneous_inequality_available"]:
        raise ValueError("simultaneous inequality must remain unavailable")
    if MISSING_SIMULTANEOUS_INEQUALITY not in summary["open_rows"]:
        raise ValueError("missing simultaneous inequality row must remain open")
    if summary["invariant_failures"]:
        raise ValueError("; ".join(summary["invariant_failures"]))


def build_report(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 141 Commutator Domination Inequality",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Gate: `{summary['gate']}`",
        f"- Positive nonhomogeneous term: `{summary['positive_nonhomogeneous_term']}`",
        f"- Required theorem: `{summary['required_theorem']}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Proved theorem: `{str(summary['proved_theorem']).lower()}`",
        f"- Global barrier closed: `{str(summary['global_barrier_closed']).lower()}`",
        f"- Full Clay NS solved: `{str(summary['full_clay_ns_solved']).lower()}`",
        f"- Clay Navier-Stokes promoted: `{str(summary['clay_navier_stokes_promoted']).lower()}`",
        "",
        "## Barrier Equation",
        "",
        f"- `{summary['u1_equation']}`",
        f"- `{summary['v_barrier_equation']}`",
        "",
        "## Normalized Target",
        "",
        f"- `{summary['normalized_target_inequality']}`",
        "",
        "## Decision",
        "",
        (
            "The ledger derives the normalized domination inequality as an "
            "obligation, but the simultaneous log-aware theorem is missing. "
            "Validation is fail-closed and emits no proof, no global barrier, "
            "and no Clay promotion."
        ),
        "",
        "## Rows",
        "",
        "| Row | Status | Role | Symbol | Budget Entry | Missing Evidence |",
        "| --- | --- | --- | --- | --- | --- |",
    ]
    for row in rows:
        entry = row["normalized_budget_entry"].replace("|", "\\|")
        missing = "; ".join(row["missing_evidence"]).replace("|", "\\|")
        lines.append(
            f"| `{row['row_id']}` | `{row['inequality_status']}` | "
            f"`{row['ledger_role']}` | `{row['normalized_symbol']}` | "
            f"{entry} | {missing} |"
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
                "contract": summary["contract"],
                "exit_code": summary["exit_code"],
                "full_clay_ns_solved": summary["full_clay_ns_solved"],
                "global_barrier_closed": summary["global_barrier_closed"],
                "proved_theorem": summary["proved_theorem"],
                "route_decision": summary["route_decision"],
                "simultaneous_inequality_available": summary[
                    "simultaneous_inequality_available"
                ],
            },
            sort_keys=True,
        )
    )
    return int(summary["exit_code"])


if __name__ == "__main__":
    sys.exit(main())
