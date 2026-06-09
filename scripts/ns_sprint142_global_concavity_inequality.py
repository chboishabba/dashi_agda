#!/usr/bin/env python3
"""Sprint 142 global concavity inequality ledger.

This deterministic stdlib emitter normalizes the inequality needed for
GlobalConcavityOfPsi1 on the complete admissible v-barrier crossing set:

    partial_z^2 psi1 <= -kappa_concavity

The rows keep the Sprint 140 scale, time-window, and boundary compatibility
constants explicit.  This is an obligation ledger, not a proof: local Taylor
concavity, elliptic nonlocal source terms, annular/boundary terms, and
tail/persistence controls are recorded as open until a simultaneous global
concavity theorem is supplied.  Validation is fail-closed and emits no global
barrier closure or Clay Navier-Stokes promotion.
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


CONTRACT = "ns_sprint142_global_concavity_inequality"
GATE = "GlobalConcavityOfPsi1"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint142_global_concavity_inequality")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"

SPRINT = 142
AFTER_SPRINT = 140
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
VARIABLE = "v = partial_z u1"
TARGET_QUANTITY = "partial_z^2 psi1"
NORMALIZED_TARGET_INEQUALITY = (
    "partial_z^2 psi1(t,r,z) <= -kappa_concavity "
    "for every (t,r,z) in AdmissibleVBarrierCrossingSet"
)
V_BARRIER_EQUATION = (
    "D_t v = nu Ltilde v + 2 v partial_z psi1 + 2 u1 partial_z^2 psi1 "
    "- (partial_z u^r) partial_r u1 - (partial_z u^z) v"
)
ELLIPTIC_RELATION = "-Ltilde psi1 = omega1"

ROUTE_DECISION = "fail_closed_missing_global_concavity_inequality"
PROMOTION_DECISION = "hold_no_clay_promotion"
REQUIRED_THEOREM = "SimultaneousGlobalConcavityOfPsi1OnAdmissibleVBarrierCrossingSet"

LOCAL_TAYLOR_MARGIN = "local_taylor_concavity_margin"
ELLIPTIC_NONLOCAL_SOURCE = "elliptic_nonlocal_source_contribution"
ANNULAR_BOUNDARY = "annular_boundary_contribution"
TAIL_PERSISTENCE = "tail_persistence_window"
MISSING_SIMULTANEOUS_THEOREM = "missing_simultaneous_concavity_theorem"

REQUIRED_ROW_IDS = {
    LOCAL_TAYLOR_MARGIN,
    ELLIPTIC_NONLOCAL_SOURCE,
    ANNULAR_BOUNDARY,
    TAIL_PERSISTENCE,
    MISSING_SIMULTANEOUS_THEOREM,
}

SPRINT_140_CONSTANTS = {
    "active_scale": "active_scale_shared_with_sprint140",
    "crossing_set": "AdmissibleVBarrierCrossingSet",
    "time_window": "T_barrier_shared_with_sprint140",
    "boundary_regime": "axis_annulus_boundary_regime_shared_with_sprint140",
    "concavity_margin": "kappa_concavity",
    "commutator_margin": "kappa_comm",
    "diffusion_margin": "kappa_diffusion",
    "strain_budget": "C_strain",
    "log_loss": "Log_BS(active_scale)",
    "slack": "strict_positive_slack",
}

SOURCE_ARTIFACTS = {
    "sprint138_global_concavity_blocker": (
        "outputs/ns_sprint138_global_concavity_blocker/"
        "ns_sprint138_global_concavity_blocker_summary.json"
    ),
    "sprint140_conditional_barrier_assembly": (
        "outputs/ns_sprint140_conditional_barrier_assembly/"
        "ns_sprint140_conditional_barrier_assembly_summary.json"
    ),
    "sprint140_constant_compatibility_ledger": (
        "outputs/ns_sprint140_constant_compatibility_ledger/"
        "ns_sprint140_constant_compatibility_ledger_summary.json"
    ),
    "sprint141_commutator_domination_inequality": (
        "outputs/ns_sprint141_commutator_domination_inequality/"
        "ns_sprint141_commutator_domination_inequality_summary.json"
    ),
}


@dataclass(frozen=True)
class ConcavityInequalityRow:
    row_id: str
    ledger_role: str
    normalized_symbol: str
    crossing_set_scope: str
    sprint140_constant_interface: tuple[str, ...]
    term_or_region: str
    required_bound: str
    available_evidence: tuple[str, ...]
    missing_evidence: tuple[str, ...]
    inequality_status: str
    contributes_local_margin: bool
    contributes_nonlocal_load: bool
    boundary_sensitive: bool
    tail_or_persistence_sensitive: bool
    simultaneous_required: bool
    theorem_available: bool
    theorem_proved: bool
    proof_closed: bool
    global_concavity_proved: bool
    global_barrier_closed: bool
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row["sprint140_constant_interface"] = list(self.sprint140_constant_interface)
        row["available_evidence"] = list(self.available_evidence)
        row["missing_evidence"] = list(self.missing_evidence)
        row["required_theorem"] = REQUIRED_THEOREM
        row["normalized_target_inequality"] = NORMALIZED_TARGET_INEQUALITY
        row["same_scale_time_boundary_constants_as_sprint140"] = True
        row["constants_absent"] = True
        row["local_support"] = self.contributes_local_margin
        row["nonlocal_adverse_obstruction"] = self.contributes_nonlocal_load
        row["simultaneous_theorem_absent"] = True
        row["global_concavity_closed"] = self.global_concavity_proved
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


def file_sha256(path: Path) -> str | None:
    if not path.exists():
        return None
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def sprint140_interface(*extra: str) -> tuple[str, ...]:
    base = (
        "active_scale_shared_with_sprint140",
        "AdmissibleVBarrierCrossingSet",
        "T_barrier_shared_with_sprint140",
        "axis_annulus_boundary_regime_shared_with_sprint140",
        "kappa_concavity",
    )
    return base + extra


def build_rows() -> list[dict[str, Any]]:
    rows = [
        ConcavityInequalityRow(
            row_id=LOCAL_TAYLOR_MARGIN,
            ledger_role="local_center_margin_candidate",
            normalized_symbol="kappa_local",
            crossing_set_scope="local_symmetry_center_patch_only",
            sprint140_constant_interface=sprint140_interface("local_patch_radius"),
            term_or_region="partial_z^2 psi1 near the z-reflection symmetry center",
            required_bound=(
                "The local Taylor expansion must produce "
                "partial_z^2 psi1 <= -kappa_concavity on every admissible "
                "first positive v crossing, not only near the primary center."
            ),
            available_evidence=(
                "Sprint 138 records local Taylor concavity near the symmetry center",
                "Sprint 140 names kappa_concavity as the favorable source margin",
            ),
            missing_evidence=(
                "uniform radius covering the full admissible crossing set",
                "lower bound kappa_local >= kappa_concavity on the Sprint 140 scale",
                "exclusion of off-center first positive v crossings outside the local patch",
            ),
            inequality_status="local_margin_available_only_conditionally",
            contributes_local_margin=True,
            contributes_nonlocal_load=False,
            boundary_sensitive=False,
            tail_or_persistence_sensitive=False,
            simultaneous_required=True,
            theorem_available=False,
            theorem_proved=False,
            proof_closed=False,
            global_concavity_proved=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        ConcavityInequalityRow(
            row_id=ELLIPTIC_NONLOCAL_SOURCE,
            ledger_role="elliptic_nonlocal_source_budget",
            normalized_symbol="N_elliptic",
            crossing_set_scope="all_sources_affecting_each_crossing_point",
            sprint140_constant_interface=sprint140_interface("omega1_source_norm", "signed_kernel_budget"),
            term_or_region=ELLIPTIC_RELATION,
            required_bound=(
                "Every nonlocal omega1 contribution to partial_z^2 psi1 must "
                "be dominated so the total elliptic reconstruction preserves "
                "partial_z^2 psi1 <= -kappa_concavity on the active crossing set."
            ),
            available_evidence=(
                "Sprint 138 identifies the elliptic nonlocal dependence of psi1",
                "Sprint 140 keeps boundary/source compatibility as a required constant input",
            ),
            missing_evidence=(
                "signed elliptic kernel dominance theorem",
                "quantitative bound for remote omega1 contributions on the Sprint 140 scale",
                "proof that nonlocal positive contributions cannot erase kappa_concavity",
            ),
            inequality_status="nonlocal_source_sign_open",
            contributes_local_margin=False,
            contributes_nonlocal_load=True,
            boundary_sensitive=True,
            tail_or_persistence_sensitive=False,
            simultaneous_required=True,
            theorem_available=False,
            theorem_proved=False,
            proof_closed=False,
            global_concavity_proved=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        ConcavityInequalityRow(
            row_id=ANNULAR_BOUNDARY,
            ledger_role="annular_boundary_compatibility",
            normalized_symbol="B_annular",
            crossing_set_scope="axis_annulus_and_boundary_crossing_subsets",
            sprint140_constant_interface=sprint140_interface("annular_radius", "boundary_leakage_budget"),
            term_or_region="annular source mass, axis behavior, and outer boundary contribution",
            required_bound=(
                "Annular and boundary contributions must be nonpositive or "
                "absorbed into the same kappa_concavity budget at every "
                "admissible v-barrier crossing."
            ),
            available_evidence=(
                "Sprint 138 records boundary and annular contribution as open",
                "Sprint 140 requires boundary and annular compatibility for the barrier constants",
            ),
            missing_evidence=(
                "boundary-compatible comparison theorem for partial_z^2 psi1",
                "annular contribution exclusion or domination estimate",
                "shared axis/boundary regime for concavity, commutator, and diffusion budgets",
            ),
            inequality_status="annular_boundary_budget_open",
            contributes_local_margin=False,
            contributes_nonlocal_load=True,
            boundary_sensitive=True,
            tail_or_persistence_sensitive=False,
            simultaneous_required=True,
            theorem_available=False,
            theorem_proved=False,
            proof_closed=False,
            global_concavity_proved=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        ConcavityInequalityRow(
            row_id=TAIL_PERSISTENCE,
            ledger_role="tail_and_time_window_persistence",
            normalized_symbol="P_tail(T_barrier)",
            crossing_set_scope="complete_time_window_and_remote_tail",
            sprint140_constant_interface=sprint140_interface("T_barrier", "tail_decay_budget"),
            term_or_region="remote source tail and time persistence of the concavity margin",
            required_bound=(
                "The strict inequality partial_z^2 psi1 <= -kappa_concavity "
                "must persist throughout the Sprint 140 barrier time window, "
                "including remote tail effects before the first v crossing."
            ),
            available_evidence=(
                "Sprint 138 names persistence failure as a blocker",
                "Sprint 140 requires one common time window across conditional assumptions",
            ),
            missing_evidence=(
                "transport-stable concavity invariant through T_barrier",
                "tail estimate compatible with the same active scale and boundary regime",
                "proof no delayed source rearrangement destroys the margin before crossing",
            ),
            inequality_status="tail_persistence_open",
            contributes_local_margin=False,
            contributes_nonlocal_load=True,
            boundary_sensitive=True,
            tail_or_persistence_sensitive=True,
            simultaneous_required=True,
            theorem_available=False,
            theorem_proved=False,
            proof_closed=False,
            global_concavity_proved=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        ConcavityInequalityRow(
            row_id=MISSING_SIMULTANEOUS_THEOREM,
            ledger_role="simultaneous_global_concavity_gate",
            normalized_symbol="Delta_concavity = -partial_z^2 psi1 - kappa_concavity",
            crossing_set_scope="entire_admissible_v_barrier_crossing_set",
            sprint140_constant_interface=sprint140_interface(
                "local_patch_radius",
                "signed_kernel_budget",
                "annular_radius",
                "boundary_leakage_budget",
                "tail_decay_budget",
                "T_barrier",
            ),
            term_or_region=NORMALIZED_TARGET_INEQUALITY,
            required_bound=(
                "A single theorem must prove Delta_concavity >= 0 using the "
                "same scale, time window, crossing set, and boundary constants "
                "as Sprint 140."
            ),
            available_evidence=(
                "the normalized global concavity inequality is explicit",
                "all required local, nonlocal, boundary, tail, and persistence rows are named",
            ),
            missing_evidence=(
                REQUIRED_THEOREM,
                "one crossing-set theorem shared by local Taylor, elliptic source, annular boundary, and persistence controls",
                "strict positive kappa_concavity compatible with Sprint 140 constants",
                "global barrier theorem separated from local conditional bookkeeping",
            ),
            inequality_status="missing_required_theorem_fail_closed",
            contributes_local_margin=False,
            contributes_nonlocal_load=False,
            boundary_sensitive=True,
            tail_or_persistence_sensitive=True,
            simultaneous_required=True,
            theorem_available=False,
            theorem_proved=False,
            proof_closed=False,
            global_concavity_proved=False,
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
        "crossing_set_scope",
        "sprint140_constant_interface",
        "term_or_region",
        "required_bound",
        "available_evidence",
        "missing_evidence",
        "required_theorem",
        "normalized_target_inequality",
        "same_scale_time_boundary_constants_as_sprint140",
        "constants_absent",
        "local_support",
        "nonlocal_adverse_obstruction",
        "simultaneous_theorem_absent",
        "inequality_status",
        "contributes_local_margin",
        "contributes_nonlocal_load",
        "boundary_sensitive",
        "tail_or_persistence_sensitive",
        "simultaneous_required",
        "theorem_available",
        "theorem_proved",
        "proof_closed",
        "global_concavity_proved",
        "global_concavity_closed",
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
            for key in (
                "sprint140_constant_interface",
                "available_evidence",
                "missing_evidence",
            ):
                serializable[key] = "; ".join(serializable[key])
            writer.writerow(serializable)


def build_summary(repo_root: Path, rows: list[dict[str, Any]]) -> dict[str, Any]:
    row_by_id = {row["row_id"]: row for row in rows}
    missing_required = sorted(REQUIRED_ROW_IDS.difference(row_by_id))
    source_hashes = {
        key: file_sha256(repo_root / relative_path)
        for key, relative_path in SOURCE_ARTIFACTS.items()
    }
    row_hashes = {row["row_id"]: row["row_hash"] for row in rows}
    rows_hash = stable_hash(rows)
    open_rows = [
        row["row_id"]
        for row in rows
        if not row["theorem_available"] or not row["proof_closed"]
    ]

    invariant_failures: list[str] = []
    if missing_required:
        invariant_failures.append("missing_required_rows:" + ",".join(missing_required))
    if not row_by_id.get(LOCAL_TAYLOR_MARGIN, {}).get("contributes_local_margin"):
        invariant_failures.append("local_taylor_margin_not_recorded")
    if not row_by_id.get(ELLIPTIC_NONLOCAL_SOURCE, {}).get("contributes_nonlocal_load"):
        invariant_failures.append("elliptic_nonlocal_source_not_recorded")
    if not row_by_id.get(ANNULAR_BOUNDARY, {}).get("boundary_sensitive"):
        invariant_failures.append("annular_boundary_not_boundary_sensitive")
    if not row_by_id.get(TAIL_PERSISTENCE, {}).get("tail_or_persistence_sensitive"):
        invariant_failures.append("tail_persistence_not_recorded")
    if REQUIRED_THEOREM not in row_by_id.get(MISSING_SIMULTANEOUS_THEOREM, {}).get(
        "missing_evidence", []
    ):
        invariant_failures.append("missing_simultaneous_theorem_not_recorded")
    if any(row["theorem_available"] for row in rows):
        invariant_failures.append("theorem_incorrectly_available")
    if any(row["theorem_proved"] for row in rows):
        invariant_failures.append("theorem_incorrectly_proved")
    if any(row["proof_closed"] for row in rows):
        invariant_failures.append("proof_closure_detected")
    if any(row["global_concavity_proved"] for row in rows):
        invariant_failures.append("global_concavity_proof_detected")
    if any(row["global_barrier_closed"] for row in rows):
        invariant_failures.append("global_barrier_closure_detected")
    if any(row["full_clay_ns_solved"] for row in rows):
        invariant_failures.append("full_clay_ns_solved_detected")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        invariant_failures.append("clay_promotion_detected")
    if not all(row["simultaneous_required"] for row in rows):
        invariant_failures.append("non_simultaneous_row_detected")
    if not all(row["same_scale_time_boundary_constants_as_sprint140"] for row in rows):
        invariant_failures.append("sprint140_constant_interface_missing")

    invariants_passed = not invariant_failures
    return {
        "contract": CONTRACT,
        "gate": GATE,
        "sprint": SPRINT,
        "after_sprint": AFTER_SPRINT,
        "program": PROGRAM,
        "variable": VARIABLE,
        "target_quantity": TARGET_QUANTITY,
        "row_count": len(rows),
        "required_row_ids": sorted(REQUIRED_ROW_IDS),
        "elliptic_relation": ELLIPTIC_RELATION,
        "v_barrier_equation": V_BARRIER_EQUATION,
        "normalized_target_inequality": NORMALIZED_TARGET_INEQUALITY,
        "required_theorem": REQUIRED_THEOREM,
        "required_theorem_available": False,
        "required_theorem_proved": False,
        "required_theorem_proven": False,
        "required_theorem_closed": False,
        "sprint140_constants": SPRINT_140_CONSTANTS,
        "same_scale_time_boundary_constants_as_sprint140": True,
        "constants_absent": True,
        "constant_compatibility_absent": True,
        "route_decision": ROUTE_DECISION,
        "promotion_decision": PROMOTION_DECISION,
        "artifact_complete": invariants_passed,
        "fail_closed": True,
        "open_rows": open_rows,
        "local_taylor_margin_only": True,
        "elliptic_nonlocal_source_closed": False,
        "annular_boundary_contribution_closed": False,
        "tail_persistence_window_closed": False,
        "simultaneous_concavity_theorem_available": False,
        "simultaneous_concavity_theorem_proved": False,
        "global_concavity_proved": False,
        "global_concavity_proven": False,
        "global_concavity_closed": False,
        "global_barrier_closed": False,
        "global_barrier": False,
        "global_proof": False,
        "global_proof_closed": False,
        "unconditional_proof": False,
        "proved_theorem": False,
        "proof_claimed": False,
        "proof_closed": False,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "clay_promoted": False,
        "source_artifacts": SOURCE_ARTIFACTS,
        "source_summary_hashes": source_hashes,
        "row_hashes": row_hashes,
        "rows_hash": rows_hash,
        "summary_payload_hash_without_self": stable_hash(
            {
                "contract": CONTRACT,
                "required_row_ids": sorted(REQUIRED_ROW_IDS),
                "normalized_target_inequality": NORMALIZED_TARGET_INEQUALITY,
                "sprint140_constants": SPRINT_140_CONSTANTS,
                "row_hashes": row_hashes,
                "rows_hash": rows_hash,
            }
        ),
        "invariant_failures": invariant_failures,
        "invariants_passed": invariants_passed,
        "exit_code": 0 if invariants_passed else 1,
        "control_card": {
            "O": (
                "Sprint 142 lane 2 owns only "
                "scripts/ns_sprint142_global_concavity_inequality.py and "
                "outputs/ns_sprint142_global_concavity_inequality/."
            ),
            "R": (
                "Normalize the inequality partial_z^2 psi1 <= -kappa_concavity "
                "on the entire admissible v-barrier crossing set."
            ),
            "C": (
                "Deterministic stdlib Python emitter producing JSON summary, "
                "JSON rows, CSV, and Markdown with stable SHA-256 row hashes."
            ),
            "S": (
                "Rows cover local Taylor concavity margin, elliptic nonlocal "
                "source contribution, annular/boundary contribution, "
                "tail/persistence window, and the missing simultaneous "
                "concavity theorem."
            ),
            "L": (
                "Use the same Sprint 140 active scale, crossing set, time "
                "window, boundary regime, and kappa_concavity interface for "
                "every row."
            ),
            "P": (
                "Treat the artifact as the next analytic obligation ledger "
                "before any GlobalConcavityOfPsi1 closure or barrier promotion."
            ),
            "G": (
                "Validation passes only while global_concavity_proved, "
                "global_barrier_closed, full_clay_ns_solved, and "
                "clay_navier_stokes_promoted remain false."
            ),
            "F": (
                "Missing rows, mismatched Sprint 140 constants, accidental "
                "theorem/proof closure, global barrier closure, full Clay NS "
                "solve, or Clay promotion fails validation."
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
    target = summary["normalized_target_inequality"]
    if "partial_z^2 psi1" not in target or "<= -kappa_concavity" not in target:
        raise ValueError("target inequality is missing the required concavity bound")
    if summary["route_decision"] != ROUTE_DECISION or not summary["fail_closed"]:
        raise ValueError("route decision must remain fail-closed")
    if not summary["same_scale_time_boundary_constants_as_sprint140"]:
        raise ValueError("Sprint 140 constant interface must be shared")
    if summary["required_theorem_available"] or summary["required_theorem_closed"]:
        raise ValueError("required theorem must remain unavailable")
    if (
        summary["global_concavity_proved"]
        or summary["global_concavity_closed"]
        or summary["proved_theorem"]
        or summary["proof_claimed"]
        or summary["proof_closed"]
    ):
        raise ValueError("global concavity/proof closure is forbidden")
    if summary["global_barrier"] or summary["global_barrier_closed"]:
        raise ValueError("global barrier closure is forbidden")
    if summary["full_clay_ns_solved"] or summary["clay_navier_stokes_promoted"]:
        raise ValueError("Clay promotion is forbidden")
    if any(row["global_concavity_proved"] for row in rows):
        raise ValueError("row claims global concavity proved")
    if any(row["global_barrier_closed"] for row in rows):
        raise ValueError("row closes global barrier")
    if any(row["full_clay_ns_solved"] for row in rows):
        raise ValueError("row claims full Clay NS solved")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        raise ValueError("row promotes Clay Navier-Stokes")
    if not all(row["same_scale_time_boundary_constants_as_sprint140"] for row in rows):
        raise ValueError("row missing Sprint 140 constant interface")
    if summary["invariant_failures"]:
        raise ValueError("; ".join(summary["invariant_failures"]))


def build_report(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 142 Global Concavity Inequality",
        "",
        f"- Contract: `{CONTRACT}`",
        f"- Gate: `{GATE}`",
        f"- Decision: `{summary['route_decision']}`",
        f"- Target inequality: `{summary['normalized_target_inequality']}`",
        f"- Required theorem: `{summary['required_theorem']}`",
        f"- Same Sprint 140 constants: `{str(summary['same_scale_time_boundary_constants_as_sprint140']).lower()}`",
        f"- Global concavity proved: `{str(summary['global_concavity_proved']).lower()}`",
        f"- Global barrier closed: `{str(summary['global_barrier_closed']).lower()}`",
        f"- Full Clay NS solved: `{str(summary['full_clay_ns_solved']).lower()}`",
        f"- Clay Navier-Stokes promoted: `{str(summary['clay_navier_stokes_promoted']).lower()}`",
        "",
        "## Sprint 140 Constant Interface",
        "",
    ]
    for key, value in summary["sprint140_constants"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(
        [
            "",
            "## Rows",
            "",
            "| Row | Role | Symbol | Status | Required bound | Missing evidence |",
            "| --- | --- | --- | --- | --- | --- |",
        ]
    )
    for row in rows:
        required_bound = row["required_bound"].replace("|", "\\|")
        missing_evidence = "; ".join(row["missing_evidence"]).replace("|", "\\|")
        lines.append(
            f"| `{row['row_id']}` | `{row['ledger_role']}` | "
            f"`{row['normalized_symbol']}` | `{row['inequality_status']}` | "
            f"{required_bound} | {missing_evidence} |"
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
                "contract": summary["contract"],
                "full_clay_ns_solved": summary["full_clay_ns_solved"],
                "global_barrier_closed": summary["global_barrier_closed"],
                "global_concavity_proved": summary["global_concavity_proved"],
                "invariants_passed": summary["invariants_passed"],
                "out_dir": str(out_dir),
                "route_decision": summary["route_decision"],
            },
            sort_keys=True,
        )
    )
    return summary["exit_code"]


if __name__ == "__main__":
    sys.exit(main())
