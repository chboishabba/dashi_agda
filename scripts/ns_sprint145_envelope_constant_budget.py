#!/usr/bin/env python3
"""Sprint 145 comparison-envelope constant budget ledger.

This deterministic stdlib emitter aggregates the constants that would be
needed to build

    ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators

from the Sprint 140/141/142/144 obstruction surfaces.  It normalizes the
concavity margin kappa_psi, commutator constant C_comm, Biot-Savart log
factor, boundary/annular constants, residual slack, and simultaneous
compatibility requirement for the v = partial_z u1 barrier.

The artifact is intentionally fail-closed: it records no compatible
simultaneous constants, constructs no comparison envelope, closes no global
barrier, and emits no Clay Navier-Stokes promotion.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import shutil
import sys
import tempfile
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint145_envelope_constant_budget"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint145_envelope_constant_budget")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"
MANIFEST_NAME = CONTRACT + "_manifest.json"

SPRINT = 145
LANE = 3
AFTER_SPRINT = 144
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
TARGET_GATE = "ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators"
TARGET_VARIABLE = "v = partial_z u1"
MISSING_THEOREM = TARGET_GATE
DECISION = "fail_closed_no_simultaneous_envelope_constants"
PROMOTION_DECISION = "hold_no_clay_promotion"
NORMALIZED_RESIDUAL_INEQUALITY = (
    "kappa_psi - C_comm * Log_BS(active_scale) - C_boundary "
    "- C_annular - C_off_peak - C_radial - C_strain >= slack_positive"
)
ENVELOPE_TARGET = (
    "2 u1 partial_z^2 psi1 - (partial_z u^r) partial_r u1 "
    "<= -kappa_env * EnvelopeControl + lower_order_absorbable_terms"
)
V_BARRIER_EQUATION = (
    "D_t v = nu Ltilde v + 2 v partial_z psi1 + 2 u1 partial_z^2 psi1 "
    "- (partial_z u^r) partial_r u1 - (partial_z u^z) v"
)

KAPPA_PSI = "concavity_margin_kappa_psi"
C_COMM = "commutator_constant_C_comm"
LOG_BIOT_SAVART = "biot_savart_log_factor"
BOUNDARY_ANNULAR = "boundary_annular_constants"
RESIDUAL_SLACK = "residual_slack_budget"
SIMULTANEOUS_COMPATIBILITY = "simultaneous_compatibility_gate"

REQUIRED_ROW_IDS = {
    KAPPA_PSI,
    C_COMM,
    LOG_BIOT_SAVART,
    BOUNDARY_ANNULAR,
    RESIDUAL_SLACK,
    SIMULTANEOUS_COMPATIBILITY,
}

SOURCE_ARTIFACTS = {
    "sprint140_constant_compatibility": (
        "outputs/ns_sprint140_constant_compatibility_ledger/"
        "ns_sprint140_constant_compatibility_ledger_summary.json"
    ),
    "sprint141_commutator_domination": (
        "outputs/ns_sprint141_commutator_domination_inequality/"
        "ns_sprint141_commutator_domination_inequality_summary.json"
    ),
    "sprint141_log_commutator": (
        "outputs/ns_sprint141_biot_savart_log_commutator_sampler/"
        "ns_sprint141_biot_savart_log_commutator_sampler_summary.json"
    ),
    "sprint142_global_concavity": (
        "outputs/ns_sprint142_global_concavity_inequality/"
        "ns_sprint142_global_concavity_inequality_summary.json"
    ),
    "sprint142_boundary_annulus": (
        "outputs/ns_sprint142_boundary_annulus_concavity_ledger/"
        "ns_sprint142_boundary_annulus_concavity_ledger_summary.json"
    ),
    "sprint144_nonlocal_zero_number": (
        "outputs/ns_sprint144_nonlocal_source_zero_number_failure/"
        "ns_sprint144_nonlocal_source_zero_number_failure_summary.json"
    ),
}

SUMMARY_REQUIRED_FALSE = {
    "compatible_simultaneous_constants",
    "comparison_envelope_available",
    "comparison_envelope_constructed",
    "comparison_envelope_proved",
    "coupled_zero_number_theorem_proved",
    "secondary_peak_exclusion_proved",
    "global_barrier_closed",
    "full_clay_ns_solved",
    "clay_navier_stokes_promoted",
    "promotion_allowed",
}


@dataclass(frozen=True)
class ConstantBudgetRow:
    row_id: str
    constant_role: str
    normalized_symbol: str
    budget_sign: str
    source_sprints: tuple[str, ...]
    normalized_requirement: str
    present_evidence: tuple[str, ...]
    missing_evidence: tuple[str, ...]
    compatibility_hazard: tuple[str, ...]
    active_crossing_set_requirement: str
    status: str
    local_support_only: bool
    adverse_load: bool
    log_loss_sensitive: bool
    boundary_or_annular_sensitive: bool
    simultaneous_required: bool
    constants_available: bool
    compatible_with_all_constants: bool
    compatible_simultaneous_constants: bool
    comparison_envelope_available: bool
    comparison_envelope_constructed: bool
    comparison_envelope_proved: bool
    coupled_zero_number_theorem_proved: bool
    secondary_peak_exclusion_proved: bool
    global_barrier_closed: bool
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool
    promotion_allowed: bool

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        for key in (
            "source_sprints",
            "present_evidence",
            "missing_evidence",
            "compatibility_hazard",
        ):
            row[key] = list(row[key])
        row["program"] = PROGRAM
        row["target_gate"] = TARGET_GATE
        row["target_variable"] = TARGET_VARIABLE
        row["missing_theorem"] = MISSING_THEOREM
        row["v_barrier_equation"] = V_BARRIER_EQUATION
        row["envelope_target"] = ENVELOPE_TARGET
        row["normalized_residual_inequality"] = NORMALIZED_RESIDUAL_INEQUALITY
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


def display_path(path: Path, repo_root: Path) -> str:
    try:
        return str(path.relative_to(repo_root))
    except ValueError:
        return str(path)


def read_source_artifact_state(repo_root: Path) -> dict[str, dict[str, Any]]:
    state: dict[str, dict[str, Any]] = {}
    flags_to_copy = (
        "constants_available",
        "constant_compatibility_absent",
        "compatible_simultaneous_constants",
        "comparison_envelope_available",
        "comparison_envelope_constructed",
        "comparison_envelope_proved",
        "global_concavity_closed",
        "global_barrier_closed",
        "full_clay_ns_solved",
        "clay_navier_stokes_promoted",
        "promotion_allowed",
        "invariants_passed",
        "artifact_complete",
    )
    for key, relative in SOURCE_ARTIFACTS.items():
        path = repo_root / relative
        entry: dict[str, Any] = {
            "path": relative,
            "exists": path.exists(),
            "sha256": file_sha256(path),
        }
        if path.exists():
            try:
                payload = json.loads(path.read_text(encoding="utf-8"))
            except json.JSONDecodeError:
                payload = {}
            for flag in flags_to_copy:
                if flag in payload:
                    entry[flag] = payload[flag]
            if "route_decision" in payload:
                entry["route_decision"] = payload["route_decision"]
            if "decision" in payload:
                entry["decision"] = payload["decision"]
        state[key] = entry
    return state


def build_rows() -> list[dict[str, Any]]:
    rows = [
        ConstantBudgetRow(
            row_id=KAPPA_PSI,
            constant_role="favorable_nonlocal_concavity_margin",
            normalized_symbol="kappa_psi",
            budget_sign="favorable_if_global_positive",
            source_sprints=("140", "142", "144"),
            normalized_requirement=(
                "A strict lower margin kappa_psi > 0 must dominate the total "
                "positive part of 2 u1 partial_z^2 psi1 on the complete "
                "admissible first-crossing set."
            ),
            present_evidence=(
                "Sprint 140 names a concavity margin in the conditional assembly.",
                "Sprint 142 records local Taylor concavity near the symmetry center.",
                "Sprint 144 identifies partial_z^2 psi1 as a required envelope input.",
            ),
            missing_evidence=(
                "global signed-kernel dominance for partial_z^2 psi1",
                "off-peak and annular source domination by the same kappa_psi",
                "positive margin on every admissible r-z first crossing",
            ),
            compatibility_hazard=(
                "local center concavity need not cover off-center crossings",
                "elliptic reconstruction is nonlocal and sign-changing",
                "no constant survives the Sprint 144 source-zero-number interface",
            ),
            active_crossing_set_requirement=(
                "same AdmissibleVBarrierCrossingSet, active scale, boundary regime, "
                "and time window as the commutator and log budgets"
            ),
            status="local_margin_only_global_constant_absent",
            local_support_only=True,
            adverse_load=False,
            log_loss_sensitive=False,
            boundary_or_annular_sensitive=True,
            simultaneous_required=True,
            constants_available=False,
            compatible_with_all_constants=False,
            compatible_simultaneous_constants=False,
            comparison_envelope_available=False,
            comparison_envelope_constructed=False,
            comparison_envelope_proved=False,
            coupled_zero_number_theorem_proved=False,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        ConstantBudgetRow(
            row_id=C_COMM,
            constant_role="radial_commutator_domination_constant",
            normalized_symbol="C_comm",
            budget_sign="adverse_positive_part",
            source_sprints=("140", "141", "144"),
            normalized_requirement=(
                "C_comm must bound max(-(partial_z u^r) partial_r u1, 0) "
                "on the same crossings where kappa_psi is invoked."
            ),
            present_evidence=(
                "Sprint 141 isolates the positive radial commutator load.",
                "Sprint 140 requires a commutator domination margin/log-loss budget.",
                "Sprint 144 records radial commutator zero-creation as a live obstruction.",
            ),
            missing_evidence=(
                "pointwise favorable sign theorem for the commutator",
                "radial-gradient coupling bound for partial_r u1 at every crossing",
                "numerical or symbolic C_comm compatible with kappa_psi after log loss",
            ),
            compatibility_hazard=(
                "incompressibility alone gives no commutator sign",
                "radial-gradient coupling is not controlled by axial zero-number data",
                "the commutator may reinforce the nonlocal source rather than cancel it",
            ),
            active_crossing_set_requirement=(
                "same r-z crossings, radial window, and time interval as the "
                "nonlocal psi1 source envelope"
            ),
            status="commutator_constant_absent",
            local_support_only=False,
            adverse_load=True,
            log_loss_sensitive=True,
            boundary_or_annular_sensitive=False,
            simultaneous_required=True,
            constants_available=False,
            compatible_with_all_constants=False,
            compatible_simultaneous_constants=False,
            comparison_envelope_available=False,
            comparison_envelope_constructed=False,
            comparison_envelope_proved=False,
            coupled_zero_number_theorem_proved=False,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        ConstantBudgetRow(
            row_id=LOG_BIOT_SAVART,
            constant_role="near_coincident_ring_log_multiplier",
            normalized_symbol="Log_BS(active_scale)",
            budget_sign="adverse_multiplier",
            source_sprints=("141", "144"),
            normalized_requirement=(
                "The envelope must absorb C_comm * Log_BS(active_scale), or "
                "prove a cancellation removing the logarithmic Biot-Savart loss."
            ),
            present_evidence=(
                "Sprint 141 names log-aware commutator domination as missing.",
                "Sprint 144 records the Biot-Savart log hazard inside the zero-number failure.",
            ),
            missing_evidence=(
                "uniform log-loss absorption constant",
                "structural cancellation at near-coincident rings",
                "scale relation proving kappa_psi remains positive after log amplification",
            ),
            compatibility_hazard=(
                "log amplification can consume any local concavity margin",
                "the active scale can change before the first positive crossing",
                "no Sprint 145 envelope constant can be normalized without the loss",
            ),
            active_crossing_set_requirement=(
                "same active_scale and annular crossing geometry as C_comm and kappa_psi"
            ),
            status="log_loss_unabsorbed",
            local_support_only=False,
            adverse_load=True,
            log_loss_sensitive=True,
            boundary_or_annular_sensitive=True,
            simultaneous_required=True,
            constants_available=False,
            compatible_with_all_constants=False,
            compatible_simultaneous_constants=False,
            comparison_envelope_available=False,
            comparison_envelope_constructed=False,
            comparison_envelope_proved=False,
            coupled_zero_number_theorem_proved=False,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        ConstantBudgetRow(
            row_id=BOUNDARY_ANNULAR,
            constant_role="boundary_annular_leakage_budget",
            normalized_symbol="C_boundary + C_annular + C_off_peak",
            budget_sign="adverse_or_uncontrolled",
            source_sprints=("140", "142", "144"),
            normalized_requirement=(
                "Boundary, annular, and off-peak source terms must be "
                "nonpositive or strictly absorbed into the same residual budget."
            ),
            present_evidence=(
                "Sprint 140 keeps boundary/annular compatibility as a required input.",
                "Sprint 142 records annular and boundary concavity ledgers.",
                "Sprint 144 records off-peak nonlocal source as a zero-number obstruction.",
            ),
            missing_evidence=(
                "boundary-compatible kernel sign cancellation theorem",
                "annular source exclusion or domination estimate",
                "off-peak source envelope tied to the same first-crossing set",
            ),
            compatibility_hazard=(
                "boundary re-entry can bypass a local center comparison",
                "annular source mass can change the sign of partial_z^2 psi1",
                "off-peak shoulders can feed secondary positive v regions",
            ),
            active_crossing_set_requirement=(
                "same boundary regime, annular window, and off-peak exclusion surface "
                "as the zero-number barrier"
            ),
            status="boundary_annular_constants_unavailable",
            local_support_only=False,
            adverse_load=True,
            log_loss_sensitive=False,
            boundary_or_annular_sensitive=True,
            simultaneous_required=True,
            constants_available=False,
            compatible_with_all_constants=False,
            compatible_simultaneous_constants=False,
            comparison_envelope_available=False,
            comparison_envelope_constructed=False,
            comparison_envelope_proved=False,
            coupled_zero_number_theorem_proved=False,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        ConstantBudgetRow(
            row_id=RESIDUAL_SLACK,
            constant_role="strict_remaining_margin_after_all_losses",
            normalized_symbol="slack_positive",
            budget_sign="required_positive_residual",
            source_sprints=("140", "141", "142", "144"),
            normalized_requirement=(
                NORMALIZED_RESIDUAL_INEQUALITY
                + " on every admissible first positive v crossing."
            ),
            present_evidence=(
                "Sprint 140 names strict residual margin as an assembly requirement.",
                "Sprints 141/142/144 identify the loads that must be subtracted.",
            ),
            missing_evidence=(
                "positive residual inequality after all source, commutator, log, boundary, annular, and strain losses",
                "single scale/time/boundary normalization for every term",
                "proof that the residual controls lower-order terms through the crossing interval",
            ),
            compatibility_hazard=(
                "individual conditional constants can be mutually inconsistent",
                "a missing adverse term makes a positive slack claim invalid",
                "local or one-dimensional estimates do not determine the full r-z residual",
            ),
            active_crossing_set_requirement=(
                "complete admissible r-z first-crossing set with one active scale "
                "and one monitored time window"
            ),
            status="strict_residual_slack_absent",
            local_support_only=False,
            adverse_load=False,
            log_loss_sensitive=True,
            boundary_or_annular_sensitive=True,
            simultaneous_required=True,
            constants_available=False,
            compatible_with_all_constants=False,
            compatible_simultaneous_constants=False,
            comparison_envelope_available=False,
            comparison_envelope_constructed=False,
            comparison_envelope_proved=False,
            coupled_zero_number_theorem_proved=False,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        ConstantBudgetRow(
            row_id=SIMULTANEOUS_COMPATIBILITY,
            constant_role="single_envelope_compatibility_gate",
            normalized_symbol="kappa_env",
            budget_sign="gate",
            source_sprints=("140", "141", "142", "144", "145"),
            normalized_requirement=(
                "One theorem must choose kappa_psi, C_comm, Log_BS, boundary, "
                "annular, off-peak, strain, and slack constants on the same "
                "crossing set and prove the comparison envelope target."
            ),
            present_evidence=(
                "The required constants are now named in one Sprint 145 ledger.",
                "The upstream ledgers identify the exact missing inputs.",
            ),
            missing_evidence=(
                MISSING_THEOREM,
                "simultaneous satisfiability proof for all constants",
                "comparison scalar problem whose zero-number theorem applies",
                "secondary peak exclusion and global axial monotonicity theorem",
            ),
            compatibility_hazard=(
                "constants may live on different scales, windows, or boundary regimes",
                "sign-changing nonlocal source and radial commutator can reinforce",
                "without a single envelope, the coupled zero-number route has no scalar comparator",
            ),
            active_crossing_set_requirement=(
                "single normalized comparison domain for source, commutator, log, boundary, annular, and residual rows"
            ),
            status="simultaneous_compatibility_unproved_fail_closed",
            local_support_only=False,
            adverse_load=False,
            log_loss_sensitive=True,
            boundary_or_annular_sensitive=True,
            simultaneous_required=True,
            constants_available=False,
            compatible_with_all_constants=False,
            compatible_simultaneous_constants=False,
            comparison_envelope_available=False,
            comparison_envelope_constructed=False,
            comparison_envelope_proved=False,
            coupled_zero_number_theorem_proved=False,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
    ]
    return [row.as_row() for row in rows]


def build_summary(rows: list[dict[str, Any]], source_state: dict[str, dict[str, Any]]) -> dict[str, Any]:
    row_ids = [row["row_id"] for row in rows]
    missing = sorted(REQUIRED_ROW_IDS.difference(row_ids))
    extra = sorted(set(row_ids).difference(REQUIRED_ROW_IDS))
    row_hashes = {row["row_id"]: row["row_hash"] for row in rows}
    rows_hash = stable_hash(rows)
    open_rows = [
        row["row_id"]
        for row in rows
        if not row["compatible_simultaneous_constants"]
        or not row["comparison_envelope_proved"]
    ]

    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "after_sprint": AFTER_SPRINT,
        "program": PROGRAM,
        "decision": DECISION,
        "promotion_decision": PROMOTION_DECISION,
        "target_gate": TARGET_GATE,
        "target_variable": TARGET_VARIABLE,
        "missing_theorem": MISSING_THEOREM,
        "v_barrier_equation": V_BARRIER_EQUATION,
        "envelope_target": ENVELOPE_TARGET,
        "normalized_residual_inequality": NORMALIZED_RESIDUAL_INEQUALITY,
        "row_count": len(rows),
        "required_row_ids": sorted(REQUIRED_ROW_IDS),
        "observed_row_ids": row_ids,
        "missing_required_row_ids": missing,
        "extra_row_ids": extra,
        "open_rows": open_rows,
        "source_artifact_state": source_state,
        "source_artifacts": SOURCE_ARTIFACTS,
        "normalized_constants": {
            "concavity_margin": "kappa_psi",
            "commutator_constant": "C_comm",
            "biot_savart_log_factor": "Log_BS(active_scale)",
            "boundary_annular_constants": "C_boundary + C_annular + C_off_peak",
            "residual_slack": "slack_positive",
            "simultaneous_envelope_margin": "kappa_env",
        },
        "budget_rows_recorded": {
            "concavity_margin_kappa_psi": KAPPA_PSI in row_ids,
            "commutator_constant_C_comm": C_COMM in row_ids,
            "biot_savart_log_factor": LOG_BIOT_SAVART in row_ids,
            "boundary_annular_constants": BOUNDARY_ANNULAR in row_ids,
            "residual_slack_budget": RESIDUAL_SLACK in row_ids,
            "simultaneous_compatibility_gate": SIMULTANEOUS_COMPATIBILITY in row_ids,
        },
        "constants_available": False,
        "compatible_simultaneous_constants": False,
        "simultaneous_constant_budget_closed": False,
        "comparison_envelope_available": False,
        "comparison_envelope_exists": False,
        "comparison_envelope_constructed": False,
        "comparison_envelope_proved": False,
        "comparison_envelope_closed": False,
        "coupled_zero_number_theorem_proved": False,
        "secondary_peak_exclusion_proved": False,
        "global_axial_monotonicity_proved": False,
        "global_barrier_closed": False,
        "global_proof": False,
        "global_proof_closed": False,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "clay_promoted": False,
        "promotion_allowed": False,
        "no_promotion": True,
        "fail_closed": True,
        "artifact_complete": False,
        "invariants_passed": False,
        "invariant_valid": False,
        "invariant_checked": False,
        "row_hashes": row_hashes,
        "rows_hash": rows_hash,
        "control_card": {
            "O": (
                "Sprint 145 worker lane 3 owns only "
                "scripts/ns_sprint145_envelope_constant_budget.py and "
                "outputs/ns_sprint145_envelope_constant_budget/."
            ),
            "R": (
                "Aggregate and normalize the constant budget required for "
                "ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators."
            ),
            "C": (
                "Deterministic stdlib ledger emitting JSON summary, JSON rows, "
                "CSV, Markdown, and manifest through an atomic staging directory."
            ),
            "S": (
                "kappa_psi is only locally supported; C_comm, Log_BS, boundary/"
                "annular loads, and residual slack remain simultaneously unavailable."
            ),
            "L": (
                "Sprint 140 conditional constants -> Sprint 141 commutator/log "
                "hazards -> Sprint 142 nonlocal/boundary hazards -> Sprint 144 "
                "missing comparison envelope -> Sprint 145 fail-closed budget."
            ),
            "P": (
                "Use this artifact as the normalized Sprint 145 constant-budget "
                "interface, not as an envelope proof."
            ),
            "G": (
                "Validation passes only if all compatibility, envelope, barrier, "
                "Clay, and promotion flags remain false while the artifact is complete."
            ),
            "F": (
                "Missing simultaneous theorem: "
                f"{MISSING_THEOREM}; no compatible residual inequality or scalar comparator exists."
            ),
        },
    }

    failures: list[str] = []
    if missing:
        failures.append("missing_required_rows:" + ",".join(missing))
    if extra:
        failures.append("unexpected_rows:" + ",".join(extra))
    for key in SUMMARY_REQUIRED_FALSE:
        if summary[key]:
            failures.append(f"summary_{key}_must_remain_false")
    for row in rows:
        for key in SUMMARY_REQUIRED_FALSE:
            if row[key]:
                failures.append(f"row_{row['row_id']}_{key}_must_remain_false")
        if row["constants_available"]:
            failures.append(f"row_{row['row_id']}_constants_incorrectly_available")
        if row["compatible_with_all_constants"]:
            failures.append(f"row_{row['row_id']}_incorrectly_compatible")
        if row["claim_closed"] or row["claim_proved"] or row["claim_proven"]:
            failures.append(f"row_{row['row_id']}_claim_incorrectly_closed")
        if not row["missing_evidence"]:
            failures.append(f"row_{row['row_id']}_missing_evidence_absent")
        if not row["simultaneous_required"]:
            failures.append(f"row_{row['row_id']}_not_simultaneous")
    rows_blob = json.dumps(rows, sort_keys=True)
    for required_text in (
        "kappa_psi",
        "C_comm",
        "Log_BS(active_scale)",
        "C_boundary",
        "C_annular",
        "slack_positive",
        MISSING_THEOREM,
    ):
        if required_text not in rows_blob and required_text not in json.dumps(summary, sort_keys=True):
            failures.append("missing_required_text:" + required_text)
    if not summary["budget_rows_recorded"]["simultaneous_compatibility_gate"]:
        failures.append("simultaneous_compatibility_gate_not_recorded")
    if summary["constants_available"] or summary["compatible_simultaneous_constants"]:
        failures.append("summary_incorrectly_closes_constants")

    summary["invariant_failures"] = failures
    summary["invariants_passed"] = not failures
    summary["invariant_valid"] = summary["invariants_passed"]
    summary["invariant_checked"] = summary["invariants_passed"]
    summary["artifact_complete"] = not failures
    summary["summary_payload_hash_without_self"] = stable_hash(
        {
            "contract": CONTRACT,
            "required_row_ids": sorted(REQUIRED_ROW_IDS),
            "normalized_residual_inequality": NORMALIZED_RESIDUAL_INEQUALITY,
            "row_hashes": row_hashes,
            "rows_hash": rows_hash,
            "invariant_failures": failures,
        }
    )
    summary["summary_hash"] = stable_hash(
        {k: v for k, v in summary.items() if k != "summary_hash"}
    )
    return summary


def validate(rows: list[dict[str, Any]], summary: dict[str, Any]) -> None:
    errors: list[str] = []
    if not rows:
        errors.append("no rows emitted")
    for key in SUMMARY_REQUIRED_FALSE:
        if summary[key]:
            errors.append(f"{key} must remain false")
    if summary["missing_required_row_ids"]:
        errors.append(f"missing rows: {summary['missing_required_row_ids']}")
    if summary["extra_row_ids"]:
        errors.append(f"unexpected rows: {summary['extra_row_ids']}")
    if not summary["artifact_complete"]:
        errors.append("artifact_complete must be true")
    if not summary["invariants_passed"]:
        errors.append("invariants_passed must be true")
    if summary["invariant_failures"]:
        errors.extend(summary["invariant_failures"])
    if errors:
        raise ValueError("; ".join(errors))


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = (
        "row_id",
        "constant_role",
        "normalized_symbol",
        "budget_sign",
        "source_sprints",
        "normalized_requirement",
        "present_evidence",
        "missing_evidence",
        "compatibility_hazard",
        "active_crossing_set_requirement",
        "status",
        "local_support_only",
        "adverse_load",
        "log_loss_sensitive",
        "boundary_or_annular_sensitive",
        "simultaneous_required",
        "constants_available",
        "compatible_with_all_constants",
        "compatible_simultaneous_constants",
        "comparison_envelope_available",
        "comparison_envelope_constructed",
        "comparison_envelope_proved",
        "coupled_zero_number_theorem_proved",
        "secondary_peak_exclusion_proved",
        "global_barrier_closed",
        "full_clay_ns_solved",
        "clay_navier_stokes_promoted",
        "promotion_allowed",
        "program",
        "target_gate",
        "target_variable",
        "missing_theorem",
        "envelope_target",
        "normalized_residual_inequality",
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
            for key in (
                "source_sprints",
                "present_evidence",
                "missing_evidence",
                "compatibility_hazard",
            ):
                serializable[key] = "; ".join(serializable[key])
            writer.writerow({key: serializable[key] for key in fieldnames})


def write_report(path: Path, rows: list[dict[str, Any]], summary: dict[str, Any]) -> None:
    lines = [
        "# Sprint 145 Envelope Constant Budget",
        "",
        f"- Contract: `{CONTRACT}`",
        f"- Decision: `{DECISION}`",
        f"- Target gate: `{TARGET_GATE}`",
        f"- Residual inequality: `{NORMALIZED_RESIDUAL_INEQUALITY}`",
        f"- Comparison envelope available: `{summary['comparison_envelope_available']}`",
        f"- Compatible simultaneous constants: `{summary['compatible_simultaneous_constants']}`",
        f"- Full Clay NS solved: `{summary['full_clay_ns_solved']}`",
        f"- Clay promotion: `{summary['clay_navier_stokes_promoted']}`",
        "",
        "## Rows",
        "",
    ]
    for row in rows:
        lines.extend(
            [
                f"### {row['row_id']}",
                "",
                f"- Symbol: `{row['normalized_symbol']}`",
                f"- Status: `{row['status']}`",
                f"- Role: {row['constant_role']}",
                f"- Requirement: {row['normalized_requirement']}",
                f"- Missing evidence: {'; '.join(row['missing_evidence'])}",
                f"- Compatible with all constants: `{row['compatible_with_all_constants']}`",
                "",
            ]
        )
    lines.extend(
        [
            "## Control Card",
            "",
            f"- O: {summary['control_card']['O']}",
            f"- R: {summary['control_card']['R']}",
            f"- C: {summary['control_card']['C']}",
            f"- S: {summary['control_card']['S']}",
            f"- L: {summary['control_card']['L']}",
            f"- P: {summary['control_card']['P']}",
            f"- G: {summary['control_card']['G']}",
            f"- F: {summary['control_card']['F']}",
            "",
        ]
    )
    path.write_text("\n".join(lines), encoding="utf-8")


def write_manifest(
    path: Path,
    artifact_root: Path,
    public_out_dir: Path,
    repo_root: Path,
    summary: dict[str, Any],
) -> None:
    artifact_files = {
        "summary": (artifact_root / SUMMARY_NAME, public_out_dir / SUMMARY_NAME),
        "rows_json": (artifact_root / ROWS_JSON_NAME, public_out_dir / ROWS_JSON_NAME),
        "rows_csv": (artifact_root / ROWS_CSV_NAME, public_out_dir / ROWS_CSV_NAME),
        "report": (artifact_root / REPORT_NAME, public_out_dir / REPORT_NAME),
    }
    manifest = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "decision": DECISION,
        "target_gate": TARGET_GATE,
        "artifact_complete": summary["artifact_complete"],
        "invariants_passed": summary["invariants_passed"],
        "files": {
            key: {
                "path": display_path(public_path, repo_root),
                "sha256": file_sha256(staged_path),
            }
            for key, (staged_path, public_path) in artifact_files.items()
        },
        "manifest_hash_without_self": stable_hash(
            {
                "contract": CONTRACT,
                "files": {
                    key: file_sha256(staged_path)
                    for key, (staged_path, _public_path) in artifact_files.items()
                },
            }
        ),
    }
    write_json(path, manifest)


def emit(out_dir: Path, repo_root: Path) -> dict[str, Any]:
    rows = build_rows()
    source_state = read_source_artifact_state(repo_root)
    summary = build_summary(rows, source_state)
    validate(rows, summary)

    out_dir = out_dir if out_dir.is_absolute() else repo_root / out_dir
    out_dir.parent.mkdir(parents=True, exist_ok=True)
    tmp_parent = out_dir.parent
    tmp_name = f".{out_dir.name}.tmp."
    tmp_dir = Path(tempfile.mkdtemp(prefix=tmp_name, dir=tmp_parent))
    try:
        write_json(tmp_dir / SUMMARY_NAME, summary)
        write_json(tmp_dir / ROWS_JSON_NAME, rows)
        write_csv(tmp_dir / ROWS_CSV_NAME, rows)
        write_report(tmp_dir / REPORT_NAME, rows, summary)
        write_manifest(tmp_dir / MANIFEST_NAME, tmp_dir, out_dir, repo_root, summary)

        if out_dir.exists():
            shutil.rmtree(out_dir)
        os.replace(tmp_dir, out_dir)
    except Exception:
        shutil.rmtree(tmp_dir, ignore_errors=True)
        raise
    return summary


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    summary = emit(args.out_dir, repo_root)
    print(
        json.dumps(
            {
                "contract": summary["contract"],
                "decision": summary["decision"],
                "artifact_complete": summary["artifact_complete"],
                "invariants_passed": summary["invariants_passed"],
                "comparison_envelope_available": summary["comparison_envelope_available"],
                "compatible_simultaneous_constants": summary["compatible_simultaneous_constants"],
                "full_clay_ns_solved": summary["full_clay_ns_solved"],
                "clay_navier_stokes_promoted": summary["clay_navier_stokes_promoted"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"{CONTRACT}: {exc}", file=sys.stderr)
        raise SystemExit(1)
