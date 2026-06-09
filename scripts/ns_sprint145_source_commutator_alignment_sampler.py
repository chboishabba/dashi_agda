#!/usr/bin/env python3
"""Sprint 145 source/commutator alignment sampler.

This deterministic sampler classifies how the nonlocal source term

    2*u1*partial_z^2 psi1

aligns with the radial commutator

    -(partial_z u^r)*partial_r u1

in the differentiated Hou-Luo v = partial_z u1 barrier equation.  It records
favorable cancellation rows and adverse reinforcement rows, including off-peak,
annular, and boundary-sensitive scenarios.  The artifact is fail-closed: it
proves no global alignment theorem, constructs no comparison envelope, solves
no Clay Navier-Stokes problem, and emits no promotion.
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


CONTRACT = "ns_sprint145_source_commutator_alignment_sampler"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint145_source_commutator_alignment_sampler")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"
MANIFEST_NAME = CONTRACT + "_manifest.json"

SPRINT = 145
LANE = 4
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
TARGET_VARIABLE = "v = partial_z u1"
TARGET_GATE = "ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators"
PARENT_SPRINT = 144
PARENT_CONTRACT = "ns_sprint144_nonlocal_source_zero_number_failure"
DECISION = "fail_closed_alignment_sampler_no_global_theorem"
MISSING_THEOREM = "GlobalSourceCommutatorAlignmentForVBarrier"
MISSING_ENVELOPE = "ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators"
V_BARRIER_EQUATION = (
    "D_t v = nu Ltilde v + 2 v partial_z psi1 + 2 u1 partial_z^2 psi1 "
    "- (partial_z u^r) partial_r u1 - (partial_z u^z) v"
)
LOAD_BEARING_RESIDUAL = (
    "2 u1 partial_z^2 psi1 - (partial_z u^r) partial_r u1"
)

SOURCE_ARTIFACTS = {
    "sprint141_log_commutator": (
        "outputs/ns_sprint141_biot_savart_log_commutator_sampler/"
        "ns_sprint141_biot_savart_log_commutator_sampler_summary.json"
    ),
    "sprint142_kernel_sign": (
        "outputs/ns_sprint142_kernel_sign_stress_sampler/"
        "ns_sprint142_kernel_sign_stress_sampler_summary.json"
    ),
    "sprint144_nonlocal_zero_number": (
        "outputs/ns_sprint144_nonlocal_source_zero_number_failure/"
        "ns_sprint144_nonlocal_source_zero_number_failure_summary.json"
    ),
}

REQUIRED_ROW_IDS = {
    "local_core_cancellation_support",
    "local_log_bounded_cancellation_support",
    "off_peak_reinforcement_positive_source",
    "annular_grazing_reinforcement",
    "boundary_image_reinforcement",
    "mixed_annular_cancellation_not_uniform",
    "tail_commutator_reinforcement",
}

REQUIRED_GEOMETRY_CLASSES = {
    "local_core",
    "local_log_bounded",
    "off_peak",
    "annular",
    "boundary",
    "tail",
}

SUMMARY_REQUIRED_FALSE = {
    "global_alignment_theorem_proved",
    "source_commutator_alignment_theorem_proved",
    "comparison_envelope_available",
    "comparison_envelope_constructed",
    "global_barrier_closed",
    "secondary_peak_exclusion_proved",
    "global_axial_monotonicity_proved",
    "full_clay_ns_solved",
    "clay_navier_stokes_promoted",
    "promotion_allowed",
}


@dataclass(frozen=True)
class AlignmentCase:
    row_id: str
    geometry_class: str
    crossing_location: str
    u1: float
    partial_z2_psi1_proxy: float
    partial_z_ur_proxy: float
    partial_r_u1_proxy: float
    local_control_proxy: float
    log_loss_multiplier: float
    boundary_multiplier: float
    expected_alignment: str
    mechanism: str
    interpretation: str


@dataclass(frozen=True)
class AlignmentRow:
    row_id: str
    sprint: int
    lane: int
    contract: str
    program: str
    target_gate: str
    target_variable: str
    parent_sprint: int
    parent_contract: str
    geometry_class: str
    crossing_location: str
    u1: float
    partial_z2_psi1_proxy: float
    partial_z_ur_proxy: float
    partial_r_u1_proxy: float
    local_control_proxy: float
    log_loss_multiplier: float
    boundary_multiplier: float
    source_term_proxy: float
    radial_commutator_proxy: float
    combined_residual_proxy: float
    normalized_residual: float
    alignment_classification: str
    favorable_cancellation_row: bool
    adverse_reinforcement_row: bool
    off_peak_or_annular_or_boundary_row: bool
    supports_local_alignment_only: bool
    obstructs_global_alignment_theorem: bool
    expected_alignment: str
    mechanism: str
    missing_input: str
    global_alignment_theorem_proved: bool
    source_commutator_alignment_theorem_proved: bool
    comparison_envelope_available: bool
    comparison_envelope_constructed: bool
    global_barrier_closed: bool
    secondary_peak_exclusion_proved: bool
    global_axial_monotonicity_proved: bool
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool
    promotion_allowed: bool
    interpretation: str

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row["decision"] = DECISION
        row["missing_theorem"] = MISSING_THEOREM
        row["missing_comparison_envelope"] = MISSING_ENVELOPE
        row["v_barrier_equation"] = V_BARRIER_EQUATION
        row["load_bearing_residual"] = LOAD_BEARING_RESIDUAL
        row["claim_closed"] = False
        row["claim_proved"] = False
        row["claim_proven"] = False
        row["no_global_proof"] = True
        row["no_promotion"] = True
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


def file_sha256(path: Path) -> str:
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


def clean(value: float) -> float:
    if abs(value) < 1.0e-14:
        return 0.0
    return float(f"{value:.15g}")


def source_artifact_state(repo_root: Path) -> dict[str, dict[str, Any]]:
    state: dict[str, dict[str, Any]] = {}
    for key, relative in SOURCE_ARTIFACTS.items():
        path = repo_root / relative
        entry: dict[str, Any] = {
            "path": relative,
            "exists": path.exists(),
            "sha256": file_sha256(path) if path.exists() else None,
        }
        if path.exists():
            try:
                payload = json.loads(path.read_text(encoding="utf-8"))
            except json.JSONDecodeError:
                payload = {}
            for flag in (
                "log_aware_commutator_domination_proved",
                "uniform_global_negative_sign_theorem_proved",
                "global_concavity_proved",
                "comparison_envelope_available",
                "comparison_envelope_constructed",
                "global_barrier_closed",
                "full_clay_ns_solved",
                "clay_navier_stokes_promoted",
            ):
                if flag in payload:
                    entry[flag] = payload[flag]
        state[key] = entry
    return state


def sample_cases() -> tuple[AlignmentCase, ...]:
    return (
        AlignmentCase(
            row_id="local_core_cancellation_support",
            geometry_class="local_core",
            crossing_location="primary_peak_near_z_symmetry_plane",
            u1=1.0,
            partial_z2_psi1_proxy=-0.42,
            partial_z_ur_proxy=0.18,
            partial_r_u1_proxy=0.72,
            local_control_proxy=1.0,
            log_loss_multiplier=1.0,
            boundary_multiplier=1.0,
            expected_alignment="favorable_cancellation",
            mechanism="local_concavity_source_and_negative_radial_commutator",
            interpretation=(
                "Local concavity makes 2*u1*partial_z2_psi1 negative and the "
                "commutator has the same damping sign; this is support only."
            ),
        ),
        AlignmentCase(
            row_id="local_log_bounded_cancellation_support",
            geometry_class="local_log_bounded",
            crossing_location="near_primary_ring_with_separated_supports",
            u1=0.86,
            partial_z2_psi1_proxy=-0.31,
            partial_z_ur_proxy=0.11,
            partial_r_u1_proxy=0.64,
            local_control_proxy=0.8,
            log_loss_multiplier=1.25,
            boundary_multiplier=1.0,
            expected_alignment="favorable_cancellation",
            mechanism="bounded_log_commutator_remains_absorbable_in_local_row",
            interpretation=(
                "A separated local row remains damping after a mild log factor, "
                "but this does not supply a global log-aware theorem."
            ),
        ),
        AlignmentCase(
            row_id="off_peak_reinforcement_positive_source",
            geometry_class="off_peak",
            crossing_location="secondary_shoulder_candidate_away_from_main_peak",
            u1=0.74,
            partial_z2_psi1_proxy=0.39,
            partial_z_ur_proxy=-0.17,
            partial_r_u1_proxy=0.58,
            local_control_proxy=0.62,
            log_loss_multiplier=1.4,
            boundary_multiplier=1.0,
            expected_alignment="adverse_reinforcement",
            mechanism="off_peak_nonlocal_source_and_commutator_both_raise_v",
            interpretation=(
                "Off-peak elliptic feedback can make the source positive while "
                "the radial commutator also raises v, blocking global alignment."
            ),
        ),
        AlignmentCase(
            row_id="annular_grazing_reinforcement",
            geometry_class="annular",
            crossing_location="grazing_annular_window_near_coincident_rings",
            u1=0.68,
            partial_z2_psi1_proxy=0.27,
            partial_z_ur_proxy=-0.23,
            partial_r_u1_proxy=0.81,
            local_control_proxy=0.7,
            log_loss_multiplier=2.8,
            boundary_multiplier=1.0,
            expected_alignment="adverse_reinforcement",
            mechanism="annular_log_loss_amplifies_positive_commutator_residual",
            interpretation=(
                "A grazing annular configuration combines wrong-sign source "
                "with log-amplified commutator reinforcement."
            ),
        ),
        AlignmentCase(
            row_id="boundary_image_reinforcement",
            geometry_class="boundary",
            crossing_location="boundary_sensitive_annular_interval",
            u1=0.57,
            partial_z2_psi1_proxy=0.21,
            partial_z_ur_proxy=-0.19,
            partial_r_u1_proxy=0.67,
            local_control_proxy=0.55,
            log_loss_multiplier=1.65,
            boundary_multiplier=1.45,
            expected_alignment="adverse_reinforcement",
            mechanism="boundary_image_changes_signed_balance",
            interpretation=(
                "Boundary/image effects can preserve positive residual sign, "
                "so local interior cancellation cannot be globalized."
            ),
        ),
        AlignmentCase(
            row_id="mixed_annular_cancellation_not_uniform",
            geometry_class="annular",
            crossing_location="annular_same_z_shell_with_radial_separation",
            u1=0.64,
            partial_z2_psi1_proxy=-0.18,
            partial_z_ur_proxy=-0.12,
            partial_r_u1_proxy=0.5,
            local_control_proxy=0.58,
            log_loss_multiplier=1.9,
            boundary_multiplier=1.0,
            expected_alignment="mixed_cancellation_not_uniform",
            mechanism="negative_source_partially_offsets_positive_commutator",
            interpretation=(
                "An annular row can cancel rather than reinforce, which shows "
                "the sampler is not one-sided enough to become a theorem."
            ),
        ),
        AlignmentCase(
            row_id="tail_commutator_reinforcement",
            geometry_class="tail",
            crossing_location="far_tail_off_route_positive_crossing",
            u1=0.42,
            partial_z2_psi1_proxy=0.16,
            partial_z_ur_proxy=-0.14,
            partial_r_u1_proxy=0.93,
            local_control_proxy=0.44,
            log_loss_multiplier=2.15,
            boundary_multiplier=1.0,
            expected_alignment="adverse_reinforcement",
            mechanism="far_tail_source_and_radial_gradient_coupling_raise_v",
            interpretation=(
                "A far-tail crossing can pair a positive nonlocal source with "
                "radial-gradient commutator reinforcement outside local control."
            ),
        ),
    )


def classify_alignment(
    source_term: float,
    commutator_term: float,
    combined_residual: float,
) -> tuple[str, bool, bool, bool]:
    source_damping = source_term <= 0.0
    commutator_damping = commutator_term <= 0.0
    combined_damping = combined_residual <= 0.0

    if source_damping and commutator_damping and combined_damping:
        return "favorable_same_sign_damping_cancellation_support", True, False, True
    if not source_damping and not commutator_damping:
        return "adverse_same_sign_growth_reinforcement", False, True, False
    if combined_damping:
        return "mixed_cancellation_damping_but_not_uniform", True, False, True
    return "mixed_reinforcement_positive_residual", False, True, False


def build_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for case in sample_cases():
        source_term = 2.0 * case.u1 * case.partial_z2_psi1_proxy
        radial_commutator = (
            -case.partial_z_ur_proxy
            * case.partial_r_u1_proxy
            * case.log_loss_multiplier
            * case.boundary_multiplier
        )
        combined = source_term + radial_commutator
        normalized = combined / max(case.local_control_proxy, 1.0e-12)
        classification, favorable, adverse, local_support = classify_alignment(
            source_term=source_term,
            commutator_term=radial_commutator,
            combined_residual=combined,
        )
        off_peak_or_nonlocal = case.geometry_class in {"off_peak", "annular", "boundary", "tail"}
        obstructs = adverse or off_peak_or_nonlocal or case.expected_alignment != "favorable_cancellation"
        missing_input = (
            "global alignment theorem with comparison-envelope constants"
            if favorable and not off_peak_or_nonlocal
            else MISSING_ENVELOPE
        )
        row = AlignmentRow(
            row_id=case.row_id,
            sprint=SPRINT,
            lane=LANE,
            contract=CONTRACT,
            program=PROGRAM,
            target_gate=TARGET_GATE,
            target_variable=TARGET_VARIABLE,
            parent_sprint=PARENT_SPRINT,
            parent_contract=PARENT_CONTRACT,
            geometry_class=case.geometry_class,
            crossing_location=case.crossing_location,
            u1=case.u1,
            partial_z2_psi1_proxy=case.partial_z2_psi1_proxy,
            partial_z_ur_proxy=case.partial_z_ur_proxy,
            partial_r_u1_proxy=case.partial_r_u1_proxy,
            local_control_proxy=case.local_control_proxy,
            log_loss_multiplier=case.log_loss_multiplier,
            boundary_multiplier=case.boundary_multiplier,
            source_term_proxy=clean(source_term),
            radial_commutator_proxy=clean(radial_commutator),
            combined_residual_proxy=clean(combined),
            normalized_residual=clean(normalized),
            alignment_classification=classification,
            favorable_cancellation_row=favorable,
            adverse_reinforcement_row=adverse,
            off_peak_or_annular_or_boundary_row=off_peak_or_nonlocal,
            supports_local_alignment_only=local_support,
            obstructs_global_alignment_theorem=obstructs,
            expected_alignment=case.expected_alignment,
            mechanism=case.mechanism,
            missing_input=missing_input,
            global_alignment_theorem_proved=False,
            source_commutator_alignment_theorem_proved=False,
            comparison_envelope_available=False,
            comparison_envelope_constructed=False,
            global_barrier_closed=False,
            secondary_peak_exclusion_proved=False,
            global_axial_monotonicity_proved=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
            interpretation=case.interpretation,
        ).as_row()
        rows.append(row)
    return rows


def build_summary(
    rows: list[dict[str, Any]],
    upstream_state: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    row_ids = [str(row["row_id"]) for row in rows]
    missing = sorted(REQUIRED_ROW_IDS.difference(row_ids))
    extra = sorted(set(row_ids).difference(REQUIRED_ROW_IDS))
    observed_geometry = {str(row["geometry_class"]) for row in rows}
    missing_geometry = sorted(REQUIRED_GEOMETRY_CLASSES.difference(observed_geometry))
    favorable_rows = [row for row in rows if row["favorable_cancellation_row"]]
    adverse_rows = [row for row in rows if row["adverse_reinforcement_row"]]
    off_peak_rows = [
        row for row in rows if row["off_peak_or_annular_or_boundary_row"]
    ]
    obstruction_rows = [
        row for row in rows if row["obstructs_global_alignment_theorem"]
    ]
    max_positive_residual = max(float(row["combined_residual_proxy"]) for row in rows)
    min_negative_residual = min(float(row["combined_residual_proxy"]) for row in rows)

    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "program": PROGRAM,
        "decision": DECISION,
        "target_gate": TARGET_GATE,
        "target_variable": TARGET_VARIABLE,
        "parent_sprint": PARENT_SPRINT,
        "parent_contract": PARENT_CONTRACT,
        "missing_theorem": MISSING_THEOREM,
        "missing_comparison_envelope": MISSING_ENVELOPE,
        "v_barrier_equation": V_BARRIER_EQUATION,
        "load_bearing_residual": LOAD_BEARING_RESIDUAL,
        "row_count": len(rows),
        "required_row_ids": sorted(REQUIRED_ROW_IDS),
        "observed_row_ids": row_ids,
        "missing_required_row_ids": missing,
        "extra_row_ids": extra,
        "required_geometry_classes": sorted(REQUIRED_GEOMETRY_CLASSES),
        "observed_geometry_classes": sorted(observed_geometry),
        "missing_geometry_classes": missing_geometry,
        "favorable_cancellation_row_ids": [row["row_id"] for row in favorable_rows],
        "adverse_reinforcement_row_ids": [row["row_id"] for row in adverse_rows],
        "off_peak_annular_boundary_row_ids": [row["row_id"] for row in off_peak_rows],
        "obstruction_row_ids": [row["row_id"] for row in obstruction_rows],
        "max_positive_residual_proxy": clean(max_positive_residual),
        "min_negative_residual_proxy": clean(min_negative_residual),
        "has_favorable_cancellation": bool(favorable_rows),
        "has_adverse_reinforcement": bool(adverse_rows),
        "has_off_peak_annular_boundary_rows": bool(off_peak_rows),
        "upstream_artifact_state": upstream_state,
        "fail_closed": True,
        "global_alignment_theorem_proved": False,
        "source_commutator_alignment_theorem_proved": False,
        "comparison_envelope_available": False,
        "comparison_envelope_constructed": False,
        "comparison_envelope_exists": False,
        "comparison_envelope_proved": False,
        "global_barrier_closed": False,
        "secondary_peak_exclusion_proved": False,
        "global_axial_monotonicity_proved": False,
        "global_proof": False,
        "global_proof_closed": False,
        "no_global_alignment_theorem": True,
        "no_comparison_envelope": True,
        "no_global_proof": True,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "promotion_allowed": False,
        "no_promotion": True,
        "promotion_decision": "hold_no_clay_promotion",
        "artifact_complete": False,
        "invariants_passed": False,
        "invariant_valid": False,
        "invariant_checked": False,
        "invariant_failures": [],
        "control_card": {
            "O": (
                "Worker lane 4 owns only scripts/ns_sprint145_source_commutator_alignment_sampler.py "
                "and outputs/ns_sprint145_source_commutator_alignment_sampler/."
            ),
            "R": (
                "Classify favorable cancellation and adverse reinforcement for "
                "2*u1*partial_z^2 psi1 versus -(partial_z u^r)*partial_r u1."
            ),
            "C": (
                "Deterministic Python sampler emitting summary JSON, row JSON, "
                "CSV, Markdown, and manifest through an atomic staging directory."
            ),
            "S": (
                "Local rows can damp, but off-peak, annular, boundary, and tail "
                "rows produce or preserve positive residuals."
            ),
            "L": (
                "Source proxy + radial commutator proxy -> combined residual -> "
                "alignment class -> fail-closed envelope obstruction ledger."
            ),
            "P": (
                "Use this as evidence that local cancellation is not a global "
                "alignment theorem and does not construct the Sprint 145 envelope."
            ),
            "G": (
                "Validation passes only if favorable and adverse rows exist while "
                "all theorem, envelope, barrier, Clay, and promotion flags remain false."
            ),
            "F": (
                f"Missing: {MISSING_THEOREM} and {MISSING_ENVELOPE}; no global "
                "axial monotonicity or Clay promotion follows."
            ),
        },
    }

    failures: list[str] = []
    if missing:
        failures.append("missing_required_rows:" + ",".join(missing))
    if extra:
        failures.append("unexpected_rows:" + ",".join(extra))
    if missing_geometry:
        failures.append("missing_geometry_classes:" + ",".join(missing_geometry))
    if not favorable_rows:
        failures.append("favorable_cancellation_rows_missing")
    if not adverse_rows:
        failures.append("adverse_reinforcement_rows_missing")
    if not off_peak_rows:
        failures.append("off_peak_annular_boundary_rows_missing")
    if max_positive_residual <= 0.0:
        failures.append("positive_residual_rows_missing")
    if min_negative_residual >= 0.0:
        failures.append("negative_residual_rows_missing")
    for key in SUMMARY_REQUIRED_FALSE:
        if summary[key]:
            failures.append(f"summary_{key}_must_remain_false")
    for row in rows:
        for key in SUMMARY_REQUIRED_FALSE:
            if row[key]:
                failures.append(f"row_{row['row_id']}_{key}_must_remain_false")
        if row["claim_closed"] or row["claim_proved"] or row["claim_proven"]:
            failures.append(f"row_{row['row_id']}_claim_incorrectly_closed")
        if not row["no_global_proof"] or not row["no_promotion"]:
            failures.append(f"row_{row['row_id']}_missing_fail_closed_guards")

    summary["invariant_failures"] = failures
    summary["invariants_passed"] = not failures
    summary["invariant_valid"] = summary["invariants_passed"]
    summary["invariant_checked"] = summary["invariants_passed"]
    summary["artifact_complete"] = not failures
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
    if not summary["has_favorable_cancellation"]:
        errors.append("has_favorable_cancellation must be true")
    if not summary["has_adverse_reinforcement"]:
        errors.append("has_adverse_reinforcement must be true")
    if not summary["has_off_peak_annular_boundary_rows"]:
        errors.append("has_off_peak_annular_boundary_rows must be true")
    if not summary["artifact_complete"]:
        errors.append("artifact_complete must be true")
    if not summary["invariants_passed"]:
        errors.append("invariants_passed must be true")
    if summary["missing_required_row_ids"]:
        errors.append(f"missing rows: {summary['missing_required_row_ids']}")
    if summary["extra_row_ids"]:
        errors.append(f"unexpected rows: {summary['extra_row_ids']}")
    if summary["missing_geometry_classes"]:
        errors.append(f"missing geometry: {summary['missing_geometry_classes']}")
    if summary["invariant_failures"]:
        errors.extend(summary["invariant_failures"])
    if errors:
        raise ValueError("; ".join(errors))


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        raise ValueError("cannot write empty CSV")
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def format_value(value: Any) -> str:
    if isinstance(value, bool):
        return str(value).lower()
    if isinstance(value, float):
        return f"{value:.12g}"
    if isinstance(value, list):
        return ", ".join(str(item) for item in value)
    return str(value)


def write_report(path: Path, rows: list[dict[str, Any]], summary: dict[str, Any]) -> None:
    lines = [
        "# Sprint 145 Source/Commutator Alignment Sampler",
        "",
        "This artifact is a deterministic fail-closed sampler for the Sprint 145 comparison-envelope gate.",
        "",
        "## Decision",
        "",
        f"- decision: `{summary['decision']}`",
        f"- missing theorem: `{summary['missing_theorem']}`",
        f"- missing envelope: `{summary['missing_comparison_envelope']}`",
        f"- global alignment theorem proved: `{format_value(summary['global_alignment_theorem_proved'])}`",
        f"- comparison envelope available: `{format_value(summary['comparison_envelope_available'])}`",
        f"- full Clay NS solved: `{format_value(summary['full_clay_ns_solved'])}`",
        f"- Clay promotion: `{format_value(summary['clay_navier_stokes_promoted'])}`",
        "",
        "## Rows",
        "",
        "| row_id | geometry | source | commutator | residual | class |",
        "|---|---:|---:|---:|---:|---|",
    ]
    for row in rows:
        lines.append(
            "| {row_id} | {geometry_class} | {source_term_proxy:.6g} | "
            "{radial_commutator_proxy:.6g} | {combined_residual_proxy:.6g} | "
            "{alignment_classification} |".format(**row)
        )
    lines.extend(
        [
            "",
            "## Control Card",
            "",
        ]
    )
    for key, value in summary["control_card"].items():
        lines.append(f"- {key}: {value}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_manifest(path: Path, out_dir: Path, repo_root: Path, files: list[Path]) -> None:
    manifest = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "out_dir": display_path(out_dir, repo_root),
        "files": [
            {
                "path": display_path(file_path, repo_root),
                "sha256": file_sha256(file_path),
                "bytes": file_path.stat().st_size,
            }
            for file_path in files
        ],
        "manifest_hash_inputs": [display_path(file_path, repo_root) for file_path in files],
    }
    manifest["manifest_hash"] = stable_hash(manifest)
    write_json(path, manifest)


def publish_outputs(out_dir: Path, tmp_dir: Path) -> None:
    if out_dir.exists():
        shutil.rmtree(out_dir)
    out_dir.parent.mkdir(parents=True, exist_ok=True)
    os.replace(tmp_dir, out_dir)


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = repo_root / out_dir
    out_dir = out_dir.resolve()

    rows = build_rows()
    upstream = source_artifact_state(repo_root)
    summary = build_summary(rows, upstream)
    validate(rows, summary)

    staging_parent = out_dir.parent
    staging_parent.mkdir(parents=True, exist_ok=True)
    tmp_dir_path = Path(
        tempfile.mkdtemp(prefix=f".{CONTRACT}.", dir=str(staging_parent))
    )
    try:
        summary_path = tmp_dir_path / SUMMARY_NAME
        rows_json_path = tmp_dir_path / ROWS_JSON_NAME
        rows_csv_path = tmp_dir_path / ROWS_CSV_NAME
        report_path = tmp_dir_path / REPORT_NAME
        manifest_path = tmp_dir_path / MANIFEST_NAME

        write_json(summary_path, summary)
        write_json(rows_json_path, rows)
        write_csv(rows_csv_path, rows)
        write_report(report_path, rows, summary)
        write_manifest(
            manifest_path,
            out_dir,
            repo_root,
            [summary_path, rows_json_path, rows_csv_path, report_path],
        )

        publish_outputs(out_dir, tmp_dir_path)
    except Exception:
        shutil.rmtree(tmp_dir_path, ignore_errors=True)
        raise

    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"{CONTRACT}: {exc}", file=sys.stderr)
        raise SystemExit(1)
