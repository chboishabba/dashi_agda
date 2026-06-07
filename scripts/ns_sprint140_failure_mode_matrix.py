#!/usr/bin/env python3
"""Sprint 140 conditional barrier failure-mode matrix.

This deterministic emitter inventories fail-closed failure modes for the
conditional barrier assembly ranked in Sprint 139.  It records what happens
when any one of the three analytic assumptions is false, when their constants
are incompatible, and when known route hazards remain open.

The artifact is a matrix, not a proof.  It emits no global Navier-Stokes proof,
does not close the monitored conditional route, and does not promote to the
full Clay Navier-Stokes class.
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


CONTRACT = "ns_sprint140_failure_mode_matrix"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint140_failure_mode_matrix")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"

SPRINT = 140
AFTER_SPRINT = 139
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
PARENT_ROUTE = "ConditionalRegularityAssembly"
ROUTE_DECISION = "fail_closed_failure_modes_open"
PROMOTION_DECISION = "hold_no_clay_promotion"

FAILURE_MODE_ALIASES = {
    "assumption_false_global_concavity_or_kernel_dominance":
        "conditional_barrier_assumption_unproved",
    "assumption_false_secondary_peak_exclusion":
        "axisymmetric_barrier_route_open",
    "assumption_false_transport_commutator_domination":
        "pointwise_commutator_domination_open",
    "constants_incompatible_across_assumptions":
        "barrier_assembly_receipt_conditional_only",
    "off_center_first_positive_crossing":
        "global_regular_boundary_missing",
    "boundary_or_annular_kernel_sign":
        "localized_kernel_sign_open",
    "commutator_biot_savart_log_loss":
        "pointwise_commutator_domination_open",
    "monitored_route_to_full_clay_translation_absent":
        "clay_problem_promotion_blocked",
}

ASSUMPTIONS = (
    "GlobalConcavityOrKernelDominance",
    "SecondaryPeakExclusion",
    "TransportCommutatorDomination",
)

SOURCE_ARTIFACTS = {
    "route_fork_classifier": "outputs/ns_sprint139_barrier_route_fork_classifier/ns_sprint139_barrier_route_fork_classifier_summary.json",
    "kernel_sign_sampler": "outputs/ns_sprint139_localized_kernel_sign_sampler/ns_sprint139_localized_kernel_sign_sampler_summary.json",
    "commutator_sign_route": "outputs/ns_sprint139_commutator_sign_route/ns_sprint139_commutator_sign_route_summary.json",
}

REQUIRED_FAILURE_IDS = {
    "assumption_false_global_concavity_or_kernel_dominance",
    "assumption_false_secondary_peak_exclusion",
    "assumption_false_transport_commutator_domination",
    "constants_incompatible_across_assumptions",
    "off_center_first_positive_crossing",
    "boundary_or_annular_kernel_sign",
    "commutator_biot_savart_log_loss",
    "monitored_route_to_full_clay_translation_absent",
}


@dataclass(frozen=True)
class FailureModeRow:
    failure_id: str
    category: str
    trigger: str
    affected_assumptions: tuple[str, ...]
    failure_condition: str
    local_effect: str
    barrier_effect: str
    required_repair: tuple[str, ...]
    status: str
    route_decision: str
    assumption_set_satisfied: bool
    constants_compatible: bool
    monitored_route_closed: bool
    global_proof_open: bool
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool
    promotion_allowed: bool

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row["affected_assumptions"] = list(self.affected_assumptions)
        row["required_repair"] = list(self.required_repair)
        row["failure_mode"] = FAILURE_MODE_ALIASES[self.failure_id]
        row["failure_mode_id"] = FAILURE_MODE_ALIASES[self.failure_id]
        row["mode_id"] = FAILURE_MODE_ALIASES[self.failure_id]
        row["route_decision_detail"] = self.route_decision
        row["route_decision"] = (
            "fail_open"
            if self.failure_id == "monitored_route_to_full_clay_translation_absent"
            else "fail_closed"
        )
        row["blocker_id"] = self.failure_id
        row["blocker_status"] = self.status
        row["blocked_claim"] = PARENT_ROUTE
        row["missing_input"] = list(self.required_repair)
        row["claim_closed"] = False
        row["claim_proved"] = False
        row["claim_proven"] = False
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


def file_sha256(path: Path) -> str | None:
    if not path.exists():
        return None
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def build_rows() -> list[dict[str, Any]]:
    rows = [
        FailureModeRow(
            failure_id="assumption_false_global_concavity_or_kernel_dominance",
            category="single_assumption_false",
            trigger="The global concavity or kernel-dominance assumption is false.",
            affected_assumptions=("GlobalConcavityOrKernelDominance",),
            failure_condition=(
                "partial_z^2 psi1 is not controlled with the sign or dominance "
                "margin needed at every admissible first positive maximum of v."
            ),
            local_effect=(
                "The source 2 u1 partial_z^2 psi1 can contribute with the "
                "wrong sign at a crossing."
            ),
            barrier_effect=(
                "The conditional v-barrier implication is unavailable even if "
                "the other two assumptions hold."
            ),
            required_repair=(
                "global signed kernel theorem",
                "or quantitative kernel dominance theorem",
                "compatibility with boundary and annular source geometry",
            ),
            status="open_fail_closed",
            route_decision=ROUTE_DECISION,
            assumption_set_satisfied=False,
            constants_compatible=False,
            monitored_route_closed=False,
            global_proof_open=True,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        FailureModeRow(
            failure_id="assumption_false_secondary_peak_exclusion",
            category="single_assumption_false",
            trigger="The secondary-peak exclusion assumption is false.",
            affected_assumptions=("SecondaryPeakExclusion",),
            failure_condition=(
                "A shoulder, secondary axial peak, or off-primary positive "
                "maximum of v can form during the monitored barrier window."
            ),
            local_effect=(
                "The first positive crossing may occur outside the region where "
                "the conditional sign and constant ledger was assembled."
            ),
            barrier_effect=(
                "Primary-region estimates do not rule out the first positive "
                "v crossing."
            ),
            required_repair=(
                "persistent no-secondary-peak theorem",
                "or crossing-set localization theorem",
                "or a barrier valid at every off-primary maximum",
            ),
            status="open_fail_closed",
            route_decision=ROUTE_DECISION,
            assumption_set_satisfied=False,
            constants_compatible=False,
            monitored_route_closed=False,
            global_proof_open=True,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        FailureModeRow(
            failure_id="assumption_false_transport_commutator_domination",
            category="single_assumption_false",
            trigger="The transport-commutator domination assumption is false.",
            affected_assumptions=("TransportCommutatorDomination",),
            failure_condition=(
                "The positive part of -(partial_z u^r) partial_r u1 is not "
                "absorbed at every admissible first positive maximum."
            ),
            local_effect=(
                "The radial commutator remains a nonhomogeneous source for v."
            ),
            barrier_effect=(
                "The maximum-principle inequality can be violated by an "
                "uncontrolled positive commutator burst."
            ),
            required_repair=(
                "pointwise favorable commutator sign theorem",
                "or log-aware quantitative domination theorem",
                "or structural cancellation on the crossing set",
            ),
            status="open_fail_closed",
            route_decision=ROUTE_DECISION,
            assumption_set_satisfied=False,
            constants_compatible=False,
            monitored_route_closed=False,
            global_proof_open=True,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        FailureModeRow(
            failure_id="constants_incompatible_across_assumptions",
            category="interface_failure",
            trigger="All three assumptions are stated, but their constants cannot be made simultaneous.",
            affected_assumptions=ASSUMPTIONS,
            failure_condition=(
                "The concavity margin, peak-localization scale, commutator "
                "budget, viscosity scale, and log-loss constants do not close "
                "one common inequality."
            ),
            local_effect=(
                "Each input can be true in isolation while the assembled "
                "barrier has a positive remainder."
            ),
            barrier_effect=(
                "The conditional assembly fails at the interface between "
                "analytic gates."
            ),
            required_repair=(
                "single normalized constant ledger",
                "scale-uniform inequalities",
                "strict positive margin after all losses are included",
            ),
            status="open_fail_closed",
            route_decision=ROUTE_DECISION,
            assumption_set_satisfied=True,
            constants_compatible=False,
            monitored_route_closed=False,
            global_proof_open=True,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        FailureModeRow(
            failure_id="off_center_first_positive_crossing",
            category="crossing_geometry",
            trigger="The first positive v crossing occurs off-center or outside the monitored core.",
            affected_assumptions=(
                "GlobalConcavityOrKernelDominance",
                "SecondaryPeakExclusion",
            ),
            failure_condition=(
                "The crossing point is not covered by the local center expansion "
                "or the primary-peak localization assumptions."
            ),
            local_effect=(
                "Axis or center sign data does not determine the crossing-set "
                "source sign."
            ),
            barrier_effect=(
                "A monitored-route barrier cannot exclude unmonitored "
                "off-center first crossings."
            ),
            required_repair=(
                "crossing-set localization",
                "global replacement for center expansion",
                "boundary-compatible first-crossing theorem",
            ),
            status="open_fail_closed",
            route_decision=ROUTE_DECISION,
            assumption_set_satisfied=False,
            constants_compatible=False,
            monitored_route_closed=False,
            global_proof_open=True,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        FailureModeRow(
            failure_id="boundary_or_annular_kernel_sign",
            category="kernel_sign_failure",
            trigger="Boundary-sensitive or annular kernel contributions have the wrong sign.",
            affected_assumptions=("GlobalConcavityOrKernelDominance",),
            failure_condition=(
                "Nonlocal elliptic contributions to partial_z^2 psi1 include "
                "annular or boundary rows with unfavorable sign."
            ),
            local_effect=(
                "A favorable local Taylor sign does not control the full "
                "elliptic source."
            ),
            barrier_effect=(
                "The concavity input cannot be promoted from local support to "
                "global barrier closure."
            ),
            required_repair=(
                "signed global Green-kernel dominance",
                "boundary leakage exclusion",
                "annular source cancellation or quantitative absorption",
            ),
            status="open_fail_closed",
            route_decision=ROUTE_DECISION,
            assumption_set_satisfied=False,
            constants_compatible=False,
            monitored_route_closed=False,
            global_proof_open=True,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        FailureModeRow(
            failure_id="commutator_biot_savart_log_loss",
            category="commutator_budget_failure",
            trigger="The commutator estimate carries an unabsorbed Biot-Savart logarithmic loss.",
            affected_assumptions=("TransportCommutatorDomination",),
            failure_condition=(
                "The strain term partial_z u^r inherits a coincident-ring log "
                "factor not covered by the barrier margin."
            ),
            local_effect=(
                "A nominal pointwise commutator bound can exceed the available "
                "source or weight margin."
            ),
            barrier_effect=(
                "Transport-commutator domination remains open until the log "
                "loss is absorbed, canceled, or avoided."
            ),
            required_repair=(
                "no-log localized strain estimate",
                "log-aware dominance with strict constants",
                "structural cancellation of the coincident-ring contribution",
            ),
            status="open_fail_closed",
            route_decision=ROUTE_DECISION,
            assumption_set_satisfied=False,
            constants_compatible=False,
            monitored_route_closed=False,
            global_proof_open=True,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        FailureModeRow(
            failure_id="monitored_route_to_full_clay_translation_absent",
            category="promotion_boundary",
            trigger="The monitored conditional route is not translated to the full Clay class.",
            affected_assumptions=ASSUMPTIONS,
            failure_condition=(
                "Even a closed monitored Hou-Luo-style conditional route would "
                "not by itself cover arbitrary smooth finite-energy "
                "three-dimensional Navier-Stokes data."
            ),
            local_effect=(
                "Route-local regularity evidence stays inside the monitored "
                "axisymmetric-with-swirl framework."
            ),
            barrier_effect=(
                "No global Clay Navier-Stokes theorem or promotion can be "
                "emitted from the conditional assembly."
            ),
            required_repair=(
                "formal monitored-route to full-class translation theorem",
                "coverage of arbitrary Clay initial data",
                "independent proof that route restrictions are exhaustive",
            ),
            status="open_fail_closed",
            route_decision=ROUTE_DECISION,
            assumption_set_satisfied=False,
            constants_compatible=False,
            monitored_route_closed=False,
            global_proof_open=True,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
    ]
    return [row.as_row() for row in rows]


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        raise ValueError("cannot write empty row set")
    fieldnames = list(rows[0].keys())
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            serializable = dict(row)
            for key in ("affected_assumptions", "required_repair", "missing_input"):
                serializable[key] = "; ".join(serializable[key])
            writer.writerow(serializable)


def build_summary(repo_root: Path, rows: list[dict[str, Any]]) -> dict[str, Any]:
    row_by_id = {row["failure_id"]: row for row in rows}
    missing_required = sorted(REQUIRED_FAILURE_IDS.difference(row_by_id))
    source_hashes = {
        key: file_sha256(repo_root / relative_path)
        for key, relative_path in SOURCE_ARTIFACTS.items()
    }
    rows_hash = stable_hash(rows)
    row_hashes = {row["failure_id"]: row["row_hash"] for row in rows}
    open_failure_modes = [
        row["failure_id"]
        for row in rows
        if row["status"] == "open_fail_closed"
    ]
    single_assumption_false_rows = [
        row["failure_id"]
        for row in rows
        if row["category"] == "single_assumption_false"
    ]

    invariant_failures: list[str] = []
    if missing_required:
        invariant_failures.append("missing_required_failures:" + ",".join(missing_required))
    if len(single_assumption_false_rows) != 3:
        invariant_failures.append("single_assumption_false_rows_not_three")
    for assumption in ASSUMPTIONS:
        if not any(
            row["category"] == "single_assumption_false"
            and assumption in row["affected_assumptions"]
            for row in rows
        ):
            invariant_failures.append("missing_single_false_case:" + assumption)
    for required_category in (
        "interface_failure",
        "crossing_geometry",
        "kernel_sign_failure",
        "commutator_budget_failure",
        "promotion_boundary",
    ):
        if not any(row["category"] == required_category for row in rows):
            invariant_failures.append("missing_category:" + required_category)
    if not all(row["route_decision_detail"] == ROUTE_DECISION for row in rows):
        invariant_failures.append("row_route_decision_mismatch")
    if any(row["monitored_route_closed"] for row in rows):
        invariant_failures.append("monitored_route_closure_detected")
    if not all(row["global_proof_open"] for row in rows):
        invariant_failures.append("global_proof_not_open_in_all_rows")
    if any(row["full_clay_ns_solved"] for row in rows):
        invariant_failures.append("full_clay_ns_solved_detected")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        invariant_failures.append("clay_promotion_detected")
    if any(row["promotion_allowed"] for row in rows):
        invariant_failures.append("promotion_allowed_detected")
    if len({row["row_hash"] for row in rows}) != len(rows):
        invariant_failures.append("row_hash_collision")

    invariants_passed = not invariant_failures
    return {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "after_sprint": AFTER_SPRINT,
        "program": PROGRAM,
        "parent_route": PARENT_ROUTE,
        "assumptions": list(ASSUMPTIONS),
        "row_count": len(rows),
        "failure_mode_count": len(rows),
        "route_decision": ROUTE_DECISION,
        "decision": ROUTE_DECISION,
        "promotion_decision": PROMOTION_DECISION,
        "fail_closed": True,
        "open_failure_modes": open_failure_modes,
        "single_assumption_false_rows": single_assumption_false_rows,
        "constants_incompatible_open": "constants_incompatible_across_assumptions" in open_failure_modes,
        "off_center_crossing_open": "off_center_first_positive_crossing" in open_failure_modes,
        "boundary_annular_kernel_sign_open": "boundary_or_annular_kernel_sign" in open_failure_modes,
        "commutator_log_loss_open": "commutator_biot_savart_log_loss" in open_failure_modes,
        "monitored_route_to_full_clay_translation_absent": (
            "monitored_route_to_full_clay_translation_absent" in open_failure_modes
        ),
        "conditional_barrier_assembly_closed": False,
        "monitored_route_closed": False,
        "global_proof": False,
        "global_proof_closed": False,
        "global_proof_open": True,
        "global_proof_proved": False,
        "global_proof_proven": False,
        "global_barrier_closed": False,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "clay_promoted": False,
        "promotion_allowed": False,
        "source_artifacts": SOURCE_ARTIFACTS,
        "source_summary_hashes": source_hashes,
        "row_hashes": row_hashes,
        "rows_hash": rows_hash,
        "summary_payload_hash_without_self": stable_hash(
            {
                "contract": CONTRACT,
                "route_decision": ROUTE_DECISION,
                "open_failure_modes": open_failure_modes,
                "source_summary_hashes": source_hashes,
                "row_hashes": row_hashes,
                "rows_hash": rows_hash,
            }
        ),
        "invariant_failures": invariant_failures,
        "invariants_passed": invariants_passed,
        "artifact_complete": invariants_passed,
        "exit_code": 0 if invariants_passed else 1,
        "control_card": {
            "O": (
                "Worker 4 owns only scripts/ns_sprint140_failure_mode_matrix.py "
                "and outputs/ns_sprint140_failure_mode_matrix/."
            ),
            "R": (
                "Inventory conditional-barrier failure modes: any one of the "
                "three assumptions false, incompatible constants, off-center "
                "crossing, boundary/annular kernel sign, commutator log loss, "
                "and absent monitored-route to full Clay translation."
            ),
            "C": (
                "Deterministic stdlib Python emitter with dataclass rows, "
                "stable SHA-256 hashes, JSON, CSV, Markdown, and fail-closed "
                "validation."
            ),
            "S": (
                "All requested failure modes are present and open; the "
                "conditional assembly, global proof, and Clay promotion remain "
                "closed only in the negative sense: no proof is emitted."
            ),
            "L": (
                "Sprint 139 route inventory -> Sprint 140 failure matrix -> "
                "open blocker rows -> no monitored-route closure -> no Clay "
                "promotion."
            ),
            "P": (
                "Use the matrix as a guardrail for conditional assembly work, "
                "not as a regularity theorem."
            ),
            "G": (
                "Validation succeeds only if route_decision is "
                "fail_closed_failure_modes_open, every failure row is open, "
                "and proof/promotion flags remain false."
            ),
            "F": (
                "Missing required failure rows, route-decision mismatch, "
                "monitored-route closure, global proof claim, full Clay NS "
                "claim, or Clay promotion fails validation."
            ),
        },
    }


def validate(summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    row_ids = {row["failure_id"] for row in rows}
    missing = REQUIRED_FAILURE_IDS.difference(row_ids)
    if missing:
        raise ValueError("missing required failure modes: " + ", ".join(sorted(missing)))
    if summary["contract"] != CONTRACT:
        raise ValueError("wrong contract")
    if summary["sprint"] != SPRINT or summary["after_sprint"] != AFTER_SPRINT:
        raise ValueError("wrong sprint metadata")
    if summary["route_decision"] != ROUTE_DECISION or not summary["fail_closed"]:
        raise ValueError("route decision must remain fail-closed")
    if summary["conditional_barrier_assembly_closed"] or summary["monitored_route_closed"]:
        raise ValueError("conditional barrier assembly must remain open")
    if not summary["global_proof_open"]:
        raise ValueError("global proof must remain open")
    if summary["global_proof_proved"] or summary["global_proof_proven"]:
        raise ValueError("global proof must not be proved")
    if summary["global_barrier_closed"]:
        raise ValueError("global barrier closure must not be claimed")
    if summary["full_clay_ns_solved"]:
        raise ValueError("full Clay NS must remain unsolved")
    if summary["clay_navier_stokes_promoted"] or summary["clay_promoted"]:
        raise ValueError("Clay promotion is forbidden")
    if summary["promotion_allowed"]:
        raise ValueError("promotion must not be allowed")
    if len(summary["single_assumption_false_rows"]) != 3:
        raise ValueError("must include exactly three single-assumption false rows")
    if not summary["constants_incompatible_open"]:
        raise ValueError("constants-incompatible failure mode must be open")
    if not summary["off_center_crossing_open"]:
        raise ValueError("off-center crossing failure mode must be open")
    if not summary["boundary_annular_kernel_sign_open"]:
        raise ValueError("boundary/annular kernel sign failure mode must be open")
    if not summary["commutator_log_loss_open"]:
        raise ValueError("commutator log-loss failure mode must be open")
    if not summary["monitored_route_to_full_clay_translation_absent"]:
        raise ValueError("Clay translation absence must be recorded")
    if not all(row["status"] == "open_fail_closed" for row in rows):
        raise ValueError("all failure rows must remain open fail-closed")
    if not all(row["route_decision_detail"] == ROUTE_DECISION for row in rows):
        raise ValueError("row route-decision mismatch")
    if any(row["monitored_route_closed"] for row in rows):
        raise ValueError("row closes monitored route")
    if not all(row["global_proof_open"] for row in rows):
        raise ValueError("row fails to keep global proof open")
    if any(row["full_clay_ns_solved"] for row in rows):
        raise ValueError("row claims full Clay NS solved")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        raise ValueError("row promotes Clay Navier-Stokes")
    if any(row["promotion_allowed"] for row in rows):
        raise ValueError("row allows promotion")
    if summary["invariant_failures"]:
        raise ValueError("; ".join(summary["invariant_failures"]))


def build_report(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 140 Failure Mode Matrix",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Sprint: `{summary['sprint']}` after Sprint `{summary['after_sprint']}`",
        f"- Parent route: `{summary['parent_route']}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Failure modes open: `{len(summary['open_failure_modes'])}`",
        f"- Conditional barrier assembly closed: `{str(summary['conditional_barrier_assembly_closed']).lower()}`",
        f"- Global proof open: `{str(summary['global_proof_open']).lower()}`",
        f"- Full Clay NS solved: `{str(summary['full_clay_ns_solved']).lower()}`",
        f"- Clay Navier-Stokes promoted: `{str(summary['clay_navier_stokes_promoted']).lower()}`",
        f"- Rows hash: `{summary['rows_hash']}`",
        "",
        "## Failure Modes",
        "",
        "| Failure | Category | Status | Trigger | Barrier Effect | Row Hash |",
        "| --- | --- | --- | --- | --- | --- |",
    ]
    for row in rows:
        trigger = row["trigger"].replace("|", "\\|")
        effect = row["barrier_effect"].replace("|", "\\|")
        lines.append(
            f"| `{row['failure_id']}` | `{row['category']}` | "
            f"`{row['status']}` | {trigger} | {effect} | `{row['row_hash']}` |"
        )
    lines.extend(["", "## Source Summary Hashes", ""])
    for key, digest in summary["source_summary_hashes"].items():
        lines.append(f"- {key}: `{digest}`")
    lines.extend(
        [
            "",
            "## Guard",
            "",
            (
                "This matrix records why the conditional barrier assembly must "
                "remain fail-closed. Any single failed assumption, incompatible "
                "constants, unresolved crossing geometry, kernel sign defect, "
                "commutator log loss, or absent full-class translation keeps "
                "the route open and blocks Clay promotion."
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
    summary = build_summary(repo_root, rows)
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
                "conditional_barrier_assembly_closed": summary[
                    "conditional_barrier_assembly_closed"
                ],
                "contract": summary["contract"],
                "exit_code": summary["exit_code"],
                "failure_mode_count": summary["failure_mode_count"],
                "full_clay_ns_solved": summary["full_clay_ns_solved"],
                "global_proof_open": summary["global_proof_open"],
                "route_decision": summary["route_decision"],
                "rows_hash": summary["rows_hash"],
            },
            sort_keys=True,
        )
    )
    return int(summary["exit_code"])


if __name__ == "__main__":
    sys.exit(main())
