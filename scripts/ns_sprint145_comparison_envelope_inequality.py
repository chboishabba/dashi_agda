#!/usr/bin/env python3
"""Sprint 145 comparison-envelope inequality emitter.

This deterministic stdlib artifact normalizes the next analytic obligation in
the symmetric Hou-Luo axisymmetric-with-swirl barrier route.  The missing
object is a single comparison envelope for the nonhomogeneous first-crossing
load in the equation for v = partial_z u1:

    Q_env = 2*u1*partial_z^2 psi1 - (partial_z u^r)*partial_r u1

At a first positive v crossing, the scalar maximum-principle/Sturm route would
need Q_env to be dominated by a strictly negative residual on the full
admissible r-z crossing set, with log-loss, radial, boundary, and annular terms
using one compatible constant budget.

This script records the desired inequality and its known obstructions.  It is
fail-closed: it emits no comparison envelope, proves no coupled zero-number
theorem, solves no full Navier-Stokes problem, and allows no Clay promotion.
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


CONTRACT = "ns_sprint145_comparison_envelope_inequality"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint145_comparison_envelope_inequality")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"
MANIFEST_NAME = CONTRACT + "_manifest.json"

SPRINT = 145
LANE = 2
AFTER_SPRINT = 144
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
TARGET_GATE = "ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators"
TARGET_VARIABLE = "v = partial_z u1"
Q_ENV = "2*u1*partial_z^2 psi1 - (partial_z u^r)*partial_r u1"
U1_EQUATION = "D_t u1 = 2 u1 partial_z psi1 + nu Ltilde u1"
V_BARRIER_EQUATION = (
    "D_t v = nu Ltilde v + 2 v partial_z psi1 + 2 u1 partial_z^2 psi1 "
    "- (partial_z u^r) partial_r u1 - (partial_z u^z) v"
)
NORMALIZED_DESIRED_INEQUALITY = (
    "Q_env(t,r,z) := 2*u1*partial_z^2 psi1 - (partial_z u^r)*partial_r u1 "
    "<= -kappa_env*EnvelopeControl(t,r,z) + LowerOrderAbsorbableTerms(t,r,z) "
    "on every point of AdmissibleCoupledVFirstCrossingSet"
)
STRICT_RESIDUAL_FORM = (
    "kappa_local_source - C_nonlocal_source - C_radial_commutator*Log_BS(active_scale) "
    "- C_boundary_annular - C_lower_order >= slack_env > 0"
)
MISSING_ENVELOPE = "ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators"
MISSING_THEOREM = "CoupledAxisymmetricZeroNumberForVBarrier"
DECISION = "fail_closed_comparison_envelope_not_available"
PROMOTION_DECISION = "hold_no_clay_promotion"

LOCAL_FAVORABLE_SOURCE = "local_favorable_source"
SIGN_CHANGING_NONLOCAL_SOURCE = "sign_changing_nonlocal_source"
RADIAL_COMMUTATOR_UNCONTROLLED = "radial_commutator_uncontrolled"
LOG_LOSS_MARGIN = "log_loss_margin"
BOUNDARY_ANNULAR_CONSTANTS = "boundary_annular_constants"
SIMULTANEOUS_RESIDUAL_MISSING = "simultaneous_residual_missing"

REQUIRED_ROW_IDS = {
    LOCAL_FAVORABLE_SOURCE,
    SIGN_CHANGING_NONLOCAL_SOURCE,
    RADIAL_COMMUTATOR_UNCONTROLLED,
    LOG_LOSS_MARGIN,
    BOUNDARY_ANNULAR_CONSTANTS,
    SIMULTANEOUS_RESIDUAL_MISSING,
}

SUMMARY_REQUIRED_FALSE = {
    "comparison_envelope_available",
    "comparison_envelope_proved",
    "coupled_zero_number_theorem_proved",
    "full_clay_ns_solved",
    "clay_navier_stokes_promoted",
}

SOURCE_ARTIFACTS = {
    "sprint141_commutator_domination_inequality": (
        "outputs/ns_sprint141_commutator_domination_inequality/"
        "ns_sprint141_commutator_domination_inequality_summary.json"
    ),
    "sprint141_biot_savart_log_commutator_sampler": (
        "outputs/ns_sprint141_biot_savart_log_commutator_sampler/"
        "ns_sprint141_biot_savart_log_commutator_sampler_summary.json"
    ),
    "sprint141_radial_gradient_coupling_ledger": (
        "outputs/ns_sprint141_radial_gradient_coupling_ledger/"
        "ns_sprint141_radial_gradient_coupling_ledger_summary.json"
    ),
    "sprint142_global_concavity_inequality": (
        "outputs/ns_sprint142_global_concavity_inequality/"
        "ns_sprint142_global_concavity_inequality_summary.json"
    ),
    "sprint142_boundary_annulus_concavity_ledger": (
        "outputs/ns_sprint142_boundary_annulus_concavity_ledger/"
        "ns_sprint142_boundary_annulus_concavity_ledger_summary.json"
    ),
    "sprint144_nonlocal_source_zero_number_failure": (
        "outputs/ns_sprint144_nonlocal_source_zero_number_failure/"
        "ns_sprint144_nonlocal_source_zero_number_failure_summary.json"
    ),
}


@dataclass(frozen=True)
class EnvelopeInequalityRow:
    row_id: str
    ledger_role: str
    normalized_symbol: str
    term_in_q_env: str
    sign_role: str
    required_bound: str
    available_support: tuple[str, ...]
    obstruction: tuple[str, ...]
    missing_input: tuple[str, ...]
    constant_interface: tuple[str, ...]
    inequality_status: str
    contributes_favorable_margin: bool
    contributes_adverse_load: bool
    nonlocal_sensitive: bool
    radial_commutator_sensitive: bool
    log_loss_sensitive: bool
    boundary_annular_sensitive: bool
    simultaneous_required: bool
    comparison_envelope_available: bool
    comparison_envelope_proved: bool
    coupled_zero_number_theorem_proved: bool
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        for key in (
            "available_support",
            "obstruction",
            "missing_input",
            "constant_interface",
        ):
            row[key] = list(row[key])
        row["program"] = PROGRAM
        row["target_gate"] = TARGET_GATE
        row["target_variable"] = TARGET_VARIABLE
        row["q_env"] = Q_ENV
        row["normalized_desired_inequality"] = NORMALIZED_DESIRED_INEQUALITY
        row["strict_residual_form"] = STRICT_RESIDUAL_FORM
        row["missing_comparison_envelope"] = MISSING_ENVELOPE
        row["missing_coupled_zero_number_theorem"] = MISSING_THEOREM
        row["same_crossing_set_scale_time_boundary_constants_required"] = True
        row["claim_closed"] = False
        row["claim_proved"] = False
        row["claim_proven"] = False
        row["promotion_allowed"] = False
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


def source_artifact_state(repo_root: Path) -> dict[str, dict[str, Any]]:
    state: dict[str, dict[str, Any]] = {}
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
            for flag in (
                "global_concavity_closed",
                "commutator_domination_closed",
                "log_biot_savart_loss_absorbed",
                "comparison_envelope_available",
                "coupled_zero_number_theorem_proved",
                "full_clay_ns_solved",
                "clay_navier_stokes_promoted",
            ):
                if flag in payload:
                    entry[flag] = payload[flag]
        state[key] = entry
    return state


def constant_interface(*extra: str) -> tuple[str, ...]:
    base = (
        "AdmissibleCoupledVFirstCrossingSet",
        "active_scale_shared_with_sprint140",
        "T_barrier_shared_with_sprint140",
        "axis_annulus_boundary_regime_shared_with_sprint140",
        "Log_BS(active_scale)",
        "slack_env",
    )
    return base + extra


def build_rows() -> list[dict[str, Any]]:
    rows = [
        EnvelopeInequalityRow(
            row_id=LOCAL_FAVORABLE_SOURCE,
            ledger_role="local_negative_source_margin_candidate",
            normalized_symbol="kappa_local_source",
            term_in_q_env="2*u1*partial_z^2 psi1 near the symmetric concentration center",
            sign_role="favorable_only_if_partial_z2_psi1_is_uniformly_negative",
            required_bound=(
                "Local concavity must give 2*u1*partial_z^2 psi1 <= "
                "-kappa_local_source*EnvelopeControl on every admissible first "
                "positive v crossing, not only at the primary symmetry-center patch."
            ),
            available_support=(
                "Sprint 137 local first-positive-crossing barrier support",
                "Sprint 138 local Taylor concavity support",
                "Sprint 142 records local_taylor_concavity_margin as a local row",
            ),
            obstruction=(
                "local support does not cover off-center r-z crossings",
                "the lower bound has not been made compatible with radial, log, boundary, and annular constants",
                "secondary shoulder crossings can occur outside the local negative-source patch",
            ),
            missing_input=(
                "uniform local-to-global source margin on the full crossing set",
                MISSING_ENVELOPE,
            ),
            constant_interface=constant_interface("kappa_local_source", "local_patch_radius"),
            inequality_status="local_support_only_not_a_global_envelope",
            contributes_favorable_margin=True,
            contributes_adverse_load=False,
            nonlocal_sensitive=False,
            radial_commutator_sensitive=False,
            log_loss_sensitive=False,
            boundary_annular_sensitive=False,
            simultaneous_required=True,
            comparison_envelope_available=False,
            comparison_envelope_proved=False,
            coupled_zero_number_theorem_proved=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        EnvelopeInequalityRow(
            row_id=SIGN_CHANGING_NONLOCAL_SOURCE,
            ledger_role="nonlocal_elliptic_source_load",
            normalized_symbol="C_nonlocal_source",
            term_in_q_env="2*u1*partial_z^2 psi1 reconstructed by the global psi1 elliptic solve",
            sign_role="adverse_when_partial_z2_psi1_has_positive_or_margin_erasing_contribution",
            required_bound=(
                "All sign-changing nonlocal contributions to partial_z^2 psi1 "
                "must either cancel or be dominated by kappa_local_source with "
                "one signed kernel estimate on the same active crossing set."
            ),
            available_support=(
                "Sprint 142 kernel and global-concavity ledgers identify the nonlocal source",
                "Sprint 144 records sign_changing_partial_z2_psi1 and off_peak_nonlocal_source hazards",
            ),
            obstruction=(
                "partial_z^2 psi1 is not globally signed",
                "off-peak omega1/u1 mass can feed psi1 at a candidate v crossing",
                "no signed elliptic kernel dominance theorem is in repo",
            ),
            missing_input=(
                "global signed kernel dominance estimate",
                "off-peak source exclusion or domination theorem",
                MISSING_ENVELOPE,
            ),
            constant_interface=constant_interface("signed_kernel_budget", "off_peak_source_budget"),
            inequality_status="sign_changing_nonlocal_source_uncontrolled",
            contributes_favorable_margin=False,
            contributes_adverse_load=True,
            nonlocal_sensitive=True,
            radial_commutator_sensitive=False,
            log_loss_sensitive=False,
            boundary_annular_sensitive=True,
            simultaneous_required=True,
            comparison_envelope_available=False,
            comparison_envelope_proved=False,
            coupled_zero_number_theorem_proved=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        EnvelopeInequalityRow(
            row_id=RADIAL_COMMUTATOR_UNCONTROLLED,
            ledger_role="radial_transport_commutator_load",
            normalized_symbol="C_radial_commutator",
            term_in_q_env="-(partial_z u^r)*partial_r u1",
            sign_role="adverse_positive_part_uncontrolled",
            required_bound=(
                "max(-(partial_z u^r)*partial_r u1, 0) must be absorbed by "
                "the same residual margin that controls the nonlocal source."
            ),
            available_support=(
                "Sprint 141 isolates the commutator positive part",
                "Sprint 141 radial-gradient coupling ledger records that axial crossing geometry does not determine partial_r u1",
                "Sprint 144 records radial_commutator_zero_creation as a zero-number transfer hazard",
            ),
            obstruction=(
                "partial_r u1 has no sign or size control from axial zero-count geometry",
                "partial_z u^r is globally coupled through velocity reconstruction",
                "incompressibility alone does not make the product sign-definite",
            ),
            missing_input=(
                "radial-gradient coupling theorem at coupled first crossings",
                "commutator positive-part domination estimate",
                MISSING_ENVELOPE,
            ),
            constant_interface=constant_interface("C_radial_commutator", "partial_r_u1_budget"),
            inequality_status="radial_commutator_positive_part_unabsorbed",
            contributes_favorable_margin=False,
            contributes_adverse_load=True,
            nonlocal_sensitive=True,
            radial_commutator_sensitive=True,
            log_loss_sensitive=True,
            boundary_annular_sensitive=False,
            simultaneous_required=True,
            comparison_envelope_available=False,
            comparison_envelope_proved=False,
            coupled_zero_number_theorem_proved=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        EnvelopeInequalityRow(
            row_id=LOG_LOSS_MARGIN,
            ledger_role="biot_savart_log_loss_budget",
            normalized_symbol="Log_BS(active_scale)",
            term_in_q_env="partial_z u^r factor inside the radial commutator",
            sign_role="adverse_multiplier_on_commutator_budget",
            required_bound=(
                "The envelope must absorb the near-coincident/off-axis "
                "axisymmetric Biot-Savart logarithm or prove a structural "
                "cancellation removing it from the active first-crossing set."
            ),
            available_support=(
                "Sprint 141 Biot-Savart log sampler records local bounded rows and log-loss hazards",
                "Sprint 144 keeps log_biot_savart_hazard open",
            ),
            obstruction=(
                "near-coincident ring geometry can amplify partial_z u^r",
                "no log-aware commutator theorem with compatible constants is present",
                "local bounded rows do not dominate all active annular scales",
            ),
            missing_input=(
                "uniform log-loss absorption constants",
                "kernel cancellation theorem at the active scale",
                MISSING_ENVELOPE,
            ),
            constant_interface=constant_interface("C_log", "near_coincident_ring_cutoff"),
            inequality_status="log_loss_margin_not_absorbed",
            contributes_favorable_margin=False,
            contributes_adverse_load=True,
            nonlocal_sensitive=True,
            radial_commutator_sensitive=True,
            log_loss_sensitive=True,
            boundary_annular_sensitive=True,
            simultaneous_required=True,
            comparison_envelope_available=False,
            comparison_envelope_proved=False,
            coupled_zero_number_theorem_proved=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        EnvelopeInequalityRow(
            row_id=BOUNDARY_ANNULAR_CONSTANTS,
            ledger_role="boundary_annular_constant_compatibility",
            normalized_symbol="C_boundary_annular",
            term_in_q_env="boundary images, annular source mass, and moving active windows",
            sign_role="adverse_or_margin_erasing_unless_compatible_constants_are_supplied",
            required_bound=(
                "Boundary, axis, annular, and moving-window contributions must "
                "fit into the same strict residual inequality as source and "
                "commutator terms."
            ),
            available_support=(
                "Sprint 142 boundary/annulus ledger records boundary-compatible concavity blockers",
                "Sprint 144 records moving boundary/annular interval and r-z topology blockers",
            ),
            obstruction=(
                "annular source mass can affect partial_z^2 psi1 away from the local center",
                "moving r-z windows can re-enter regions not covered by a scalar z-line envelope",
                "constant compatibility across boundary, annular, source, and commutator terms is absent",
            ),
            missing_input=(
                "boundary-compatible kernel/sign/cancellation theorem",
                "annular migration exclusion or absorption constants",
                "single constant ledger with positive slack_env",
            ),
            constant_interface=constant_interface("C_boundary_annular", "annular_radius", "boundary_leakage_budget"),
            inequality_status="boundary_annular_constants_absent",
            contributes_favorable_margin=False,
            contributes_adverse_load=True,
            nonlocal_sensitive=True,
            radial_commutator_sensitive=False,
            log_loss_sensitive=False,
            boundary_annular_sensitive=True,
            simultaneous_required=True,
            comparison_envelope_available=False,
            comparison_envelope_proved=False,
            coupled_zero_number_theorem_proved=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        EnvelopeInequalityRow(
            row_id=SIMULTANEOUS_RESIDUAL_MISSING,
            ledger_role="simultaneous_comparison_envelope_gate",
            normalized_symbol="Delta_env",
            term_in_q_env=STRICT_RESIDUAL_FORM,
            sign_role="must_be_strictly_positive_after_all_loads",
            required_bound=(
                "One theorem must prove Delta_env >= slack_env > 0 for every "
                "point of AdmissibleCoupledVFirstCrossingSet using the same "
                "scale, time window, boundary regime, kernel decomposition, "
                "and radial-gradient budget."
            ),
            available_support=(
                "Sprints 141, 142, and 144 name the separate source, commutator, log, and boundary hazards",
                "Sprint 145 target inequality is now normalized as Q_env <= negative envelope residual",
            ),
            obstruction=(
                "the separate ledgers do not combine into one signed residual",
                "no compatible constants show the favorable source margin survives all adverse loads",
                "without this envelope, coupled zero-number transfer and secondary-peak exclusion remain unproved",
            ),
            missing_input=(
                MISSING_ENVELOPE,
                MISSING_THEOREM,
                "SecondaryPeakExclusion",
                "GlobalAxialMonotonicityOfSwirlProfile",
            ),
            constant_interface=constant_interface(
                "kappa_local_source",
                "C_nonlocal_source",
                "C_radial_commutator",
                "C_boundary_annular",
                "C_lower_order",
            ),
            inequality_status="missing_simultaneous_residual_fail_closed",
            contributes_favorable_margin=False,
            contributes_adverse_load=False,
            nonlocal_sensitive=True,
            radial_commutator_sensitive=True,
            log_loss_sensitive=True,
            boundary_annular_sensitive=True,
            simultaneous_required=True,
            comparison_envelope_available=False,
            comparison_envelope_proved=False,
            coupled_zero_number_theorem_proved=False,
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
        "term_in_q_env",
        "sign_role",
        "required_bound",
        "available_support",
        "obstruction",
        "missing_input",
        "constant_interface",
        "program",
        "target_gate",
        "target_variable",
        "q_env",
        "normalized_desired_inequality",
        "strict_residual_form",
        "missing_comparison_envelope",
        "missing_coupled_zero_number_theorem",
        "same_crossing_set_scale_time_boundary_constants_required",
        "inequality_status",
        "contributes_favorable_margin",
        "contributes_adverse_load",
        "nonlocal_sensitive",
        "radial_commutator_sensitive",
        "log_loss_sensitive",
        "boundary_annular_sensitive",
        "simultaneous_required",
        "comparison_envelope_available",
        "comparison_envelope_proved",
        "coupled_zero_number_theorem_proved",
        "full_clay_ns_solved",
        "clay_navier_stokes_promoted",
        "claim_closed",
        "claim_proved",
        "claim_proven",
        "promotion_allowed",
        "row_hash",
    )
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            serializable = dict(row)
            for key in (
                "available_support",
                "obstruction",
                "missing_input",
                "constant_interface",
            ):
                serializable[key] = "; ".join(serializable[key])
            writer.writerow(serializable)


def build_summary(rows: list[dict[str, Any]], source_state: dict[str, dict[str, Any]]) -> dict[str, Any]:
    row_by_id = {row["row_id"]: row for row in rows}
    missing_required = sorted(REQUIRED_ROW_IDS.difference(row_by_id))
    extra_rows = sorted(set(row_by_id).difference(REQUIRED_ROW_IDS))
    row_hashes = {row["row_id"]: row["row_hash"] for row in rows}
    rows_hash = stable_hash(rows)
    favorable_rows = [row["row_id"] for row in rows if row["contributes_favorable_margin"]]
    adverse_rows = [row["row_id"] for row in rows if row["contributes_adverse_load"]]
    open_rows = [
        row["row_id"]
        for row in rows
        if not row["comparison_envelope_available"] or not row["comparison_envelope_proved"]
    ]

    invariant_failures: list[str] = []
    if missing_required:
        invariant_failures.append("missing_required_rows:" + ",".join(missing_required))
    if extra_rows:
        invariant_failures.append("unexpected_rows:" + ",".join(extra_rows))
    if not row_by_id.get(LOCAL_FAVORABLE_SOURCE, {}).get("contributes_favorable_margin"):
        invariant_failures.append("local_favorable_source_margin_not_recorded")
    for row_id in (
        SIGN_CHANGING_NONLOCAL_SOURCE,
        RADIAL_COMMUTATOR_UNCONTROLLED,
        LOG_LOSS_MARGIN,
        BOUNDARY_ANNULAR_CONSTANTS,
    ):
        if not row_by_id.get(row_id, {}).get("contributes_adverse_load"):
            invariant_failures.append(f"{row_id}_not_recorded_as_adverse_load")
    if not row_by_id.get(SIGN_CHANGING_NONLOCAL_SOURCE, {}).get("nonlocal_sensitive"):
        invariant_failures.append("sign_changing_nonlocal_source_not_nonlocal_sensitive")
    if not row_by_id.get(RADIAL_COMMUTATOR_UNCONTROLLED, {}).get("radial_commutator_sensitive"):
        invariant_failures.append("radial_commutator_not_radial_sensitive")
    if not row_by_id.get(LOG_LOSS_MARGIN, {}).get("log_loss_sensitive"):
        invariant_failures.append("log_loss_margin_not_log_sensitive")
    if not row_by_id.get(BOUNDARY_ANNULAR_CONSTANTS, {}).get("boundary_annular_sensitive"):
        invariant_failures.append("boundary_annular_constants_not_boundary_sensitive")
    if MISSING_ENVELOPE not in row_by_id.get(SIMULTANEOUS_RESIDUAL_MISSING, {}).get(
        "missing_input", []
    ):
        invariant_failures.append("missing_envelope_not_recorded")
    if MISSING_THEOREM not in row_by_id.get(SIMULTANEOUS_RESIDUAL_MISSING, {}).get(
        "missing_input", []
    ):
        invariant_failures.append("missing_coupled_zero_number_not_recorded")
    if any(row["comparison_envelope_available"] for row in rows):
        invariant_failures.append("comparison_envelope_incorrectly_available")
    if any(row["comparison_envelope_proved"] for row in rows):
        invariant_failures.append("comparison_envelope_incorrectly_proved")
    if any(row["coupled_zero_number_theorem_proved"] for row in rows):
        invariant_failures.append("coupled_zero_number_theorem_incorrectly_proved")
    if any(row["full_clay_ns_solved"] for row in rows):
        invariant_failures.append("full_clay_ns_solved_detected")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        invariant_failures.append("clay_promotion_detected")
    if any(row["claim_closed"] or row["claim_proved"] or row["claim_proven"] for row in rows):
        invariant_failures.append("claim_closure_detected")
    if any(row["promotion_allowed"] for row in rows):
        invariant_failures.append("promotion_allowed_detected")
    if not all(row["simultaneous_required"] for row in rows):
        invariant_failures.append("non_simultaneous_row_detected")
    if Q_ENV not in NORMALIZED_DESIRED_INEQUALITY:
        invariant_failures.append("q_env_not_in_normalized_inequality")

    invariants_passed = not invariant_failures
    summary = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "after_sprint": AFTER_SPRINT,
        "program": PROGRAM,
        "target_gate": TARGET_GATE,
        "target_variable": TARGET_VARIABLE,
        "q_env": Q_ENV,
        "u1_equation": U1_EQUATION,
        "v_barrier_equation": V_BARRIER_EQUATION,
        "normalized_desired_inequality": NORMALIZED_DESIRED_INEQUALITY,
        "strict_residual_form": STRICT_RESIDUAL_FORM,
        "missing_comparison_envelope": MISSING_ENVELOPE,
        "missing_coupled_zero_number_theorem": MISSING_THEOREM,
        "decision": DECISION,
        "promotion_decision": PROMOTION_DECISION,
        "row_count": len(rows),
        "required_row_ids": sorted(REQUIRED_ROW_IDS),
        "observed_row_ids": [row["row_id"] for row in rows],
        "missing_required_row_ids": missing_required,
        "extra_row_ids": extra_rows,
        "favorable_margin_rows": favorable_rows,
        "adverse_load_rows": adverse_rows,
        "open_rows": open_rows,
        "source_artifact_state": source_state,
        "comparison_envelope_available": False,
        "comparison_envelope_exists": False,
        "comparison_envelope_constructed": False,
        "comparison_envelope_proved": False,
        "comparison_envelope_proven": False,
        "comparison_envelope_closed": False,
        "coupled_zero_number_theorem_available": False,
        "coupled_zero_number_theorem_proved": False,
        "coupled_zero_number_theorem_proven": False,
        "coupled_zero_number_theorem_closed": False,
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
        "artifact_complete": invariants_passed,
        "invariants_passed": invariants_passed,
        "invariant_valid": invariants_passed,
        "invariant_checked": True,
        "invariant_failures": invariant_failures,
        "row_hashes": row_hashes,
        "rows_hash": rows_hash,
        "summary_payload_hash_without_self": stable_hash(
            {
                "contract": CONTRACT,
                "required_row_ids": sorted(REQUIRED_ROW_IDS),
                "normalized_desired_inequality": NORMALIZED_DESIRED_INEQUALITY,
                "strict_residual_form": STRICT_RESIDUAL_FORM,
                "row_hashes": row_hashes,
                "rows_hash": rows_hash,
            }
        ),
        "exit_code": 0 if invariants_passed else 1,
        "control_card": {
            "O": (
                "Sprint 145 worker lane 2 owns only "
                "scripts/ns_sprint145_comparison_envelope_inequality.py and "
                "outputs/ns_sprint145_comparison_envelope_inequality/."
            ),
            "R": (
                "Normalize the desired comparison-envelope inequality for "
                "2*u1*partial_z^2 psi1 - (partial_z u^r)*partial_r u1."
            ),
            "C": (
                "Deterministic stdlib emitter producing JSON summary, JSON rows, "
                "CSV, Markdown report, and manifest with stable hashes."
            ),
            "S": (
                "Local favorable source support exists only locally; sign-changing "
                "nonlocal source, uncontrolled radial commutator, log-loss margin, "
                "and boundary/annular constants block the simultaneous residual."
            ),
            "L": (
                "Local source margin -> nonlocal source load -> radial/log load -> "
                "boundary/annular load -> missing Delta_env residual -> no coupled zero-number theorem."
            ),
            "P": (
                "Emit a fail-closed obligation ledger for the next analytic proof; "
                "do not promote it to a theorem."
            ),
            "G": (
                "Validation passes only if comparison_envelope_available/proved, "
                "coupled_zero_number_theorem_proved, full_clay_ns_solved, and "
                "clay_navier_stokes_promoted all remain false while artifact_complete is true."
            ),
            "F": (
                f"Missing {MISSING_ENVELOPE}; without it {MISSING_THEOREM}, "
                "SecondaryPeakExclusion, global axial monotonicity, and Clay promotion remain blocked."
            ),
        },
    }
    return summary


def validate(summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    if summary["contract"] != CONTRACT:
        raise ValueError("wrong contract")
    row_ids = {row["row_id"] for row in rows}
    missing = REQUIRED_ROW_IDS.difference(row_ids)
    if missing:
        raise ValueError("missing required rows: " + ", ".join(sorted(missing)))
    extra = row_ids.difference(REQUIRED_ROW_IDS)
    if extra:
        raise ValueError("unexpected rows: " + ", ".join(sorted(extra)))
    for key in SUMMARY_REQUIRED_FALSE:
        if summary[key]:
            raise ValueError(f"{key} must remain false")
    if not summary["artifact_complete"]:
        raise ValueError("artifact_complete must be true")
    if not summary["invariants_passed"]:
        raise ValueError("invariants must pass")
    if not summary["invariant_valid"] or not summary["invariant_checked"]:
        raise ValueError("invariant_valid and invariant_checked must be true")
    if summary["promotion_allowed"] or not summary["no_promotion"]:
        raise ValueError("promotion must remain forbidden")
    if summary["missing_required_row_ids"] or summary["extra_row_ids"]:
        raise ValueError("required row set mismatch")
    if summary["q_env"] != Q_ENV:
        raise ValueError("wrong q_env")
    if MISSING_ENVELOPE != summary["missing_comparison_envelope"]:
        raise ValueError("missing envelope not recorded")
    if MISSING_THEOREM != summary["missing_coupled_zero_number_theorem"]:
        raise ValueError("missing coupled theorem not recorded")
    for row in rows:
        for key in SUMMARY_REQUIRED_FALSE:
            if row[key]:
                raise ValueError(f"row {row['row_id']} incorrectly sets {key}=true")
        if row["claim_closed"] or row["claim_proved"] or row["claim_proven"]:
            raise ValueError(f"row {row['row_id']} incorrectly closes a claim")
        if row["promotion_allowed"]:
            raise ValueError(f"row {row['row_id']} incorrectly allows promotion")
    if summary["invariant_failures"]:
        raise ValueError("invariant failures present: " + ", ".join(summary["invariant_failures"]))


def build_report(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# Sprint 145 Comparison-Envelope Inequality",
        "",
        f"- Contract: `{CONTRACT}`",
        f"- Decision: `{DECISION}`",
        f"- Target gate: `{TARGET_GATE}`",
        f"- Missing coupled theorem: `{MISSING_THEOREM}`",
        f"- Promotion: `{PROMOTION_DECISION}`",
        "",
        "## Normalized Inequality",
        "",
        f"`{NORMALIZED_DESIRED_INEQUALITY}`",
        "",
        "Strict residual interface:",
        "",
        f"`{STRICT_RESIDUAL_FORM}`",
        "",
        "## Rows",
        "",
        "| row_id | role | status | favorable | adverse |",
        "|---|---|---|---:|---:|",
    ]
    for row in rows:
        lines.append(
            "| {row_id} | {ledger_role} | {inequality_status} | {fav} | {adv} |".format(
                row_id=row["row_id"],
                ledger_role=row["ledger_role"],
                inequality_status=row["inequality_status"],
                fav=str(row["contributes_favorable_margin"]).lower(),
                adv=str(row["contributes_adverse_load"]).lower(),
            )
        )
    lines.extend(
        [
            "",
            "## Fail-Closed Flags",
            "",
            f"- `comparison_envelope_available`: `{str(summary['comparison_envelope_available']).lower()}`",
            f"- `comparison_envelope_proved`: `{str(summary['comparison_envelope_proved']).lower()}`",
            f"- `coupled_zero_number_theorem_proved`: `{str(summary['coupled_zero_number_theorem_proved']).lower()}`",
            f"- `full_clay_ns_solved`: `{str(summary['full_clay_ns_solved']).lower()}`",
            f"- `clay_navier_stokes_promoted`: `{str(summary['clay_navier_stokes_promoted']).lower()}`",
            f"- `artifact_complete`: `{str(summary['artifact_complete']).lower()}`",
            f"- `invariants_passed`: `{str(summary['invariants_passed']).lower()}`",
            "",
            "## Control Card",
            "",
        ]
    )
    for key in ("O", "R", "C", "S", "L", "P", "G", "F"):
        lines.append(f"- `{key}`: {summary['control_card'][key]}")
    lines.append("")
    return "\n".join(lines)


def build_manifest(repo_root: Path, out_dir: Path, summary: dict[str, Any]) -> dict[str, Any]:
    files = {
        "summary": out_dir / SUMMARY_NAME,
        "rows_json": out_dir / ROWS_JSON_NAME,
        "rows_csv": out_dir / ROWS_CSV_NAME,
        "report": out_dir / REPORT_NAME,
    }
    return {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "decision": DECISION,
        "artifact_complete": summary["artifact_complete"],
        "invariants_passed": summary["invariants_passed"],
        "files": {
            key: {
                "path": display_path(path, repo_root),
                "sha256": file_sha256(path),
            }
            for key, path in files.items()
        },
        "manifest_payload_hash_without_self": stable_hash(
            {
                "contract": CONTRACT,
                "files": {
                    key: {
                        "path": display_path(path, repo_root),
                        "sha256": file_sha256(path),
                    }
                    for key, path in files.items()
                },
            }
        ),
    }


def atomic_emit(repo_root: Path, out_dir: Path, rows: list[dict[str, Any]], summary: dict[str, Any]) -> dict[str, Any]:
    parent = out_dir.parent
    parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=CONTRACT + ".", dir=parent) as tmp_name:
        tmp_dir = Path(tmp_name)
        write_json(tmp_dir / SUMMARY_NAME, summary)
        write_json(tmp_dir / ROWS_JSON_NAME, rows)
        write_csv(tmp_dir / ROWS_CSV_NAME, rows)
        (tmp_dir / REPORT_NAME).write_text(build_report(summary, rows), encoding="utf-8")
        manifest = build_manifest(repo_root, tmp_dir, summary)
        write_json(tmp_dir / MANIFEST_NAME, manifest)

        if out_dir.exists():
            shutil.rmtree(out_dir)
        os.replace(tmp_dir, out_dir)

    final_manifest = build_manifest(repo_root, out_dir, summary)
    write_json(out_dir / MANIFEST_NAME, final_manifest)
    return final_manifest


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = repo_root / out_dir

    rows = build_rows()
    sources = source_artifact_state(repo_root)
    summary = build_summary(rows, sources)
    validate(summary, rows)
    manifest = atomic_emit(repo_root, out_dir, rows, summary)

    print(json.dumps({"summary": summary, "manifest": manifest}, indent=2, sort_keys=True))
    return int(summary["exit_code"])


if __name__ == "__main__":
    sys.exit(main())
