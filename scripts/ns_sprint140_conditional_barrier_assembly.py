#!/usr/bin/env python3
"""Sprint 140 conditional NS barrier assembly emitter.

This deterministic artifact assembles the conditional theorem interface for
the symmetric Hou-Luo monitored route.  It does not prove the analytic
assumptions.  Instead it records the exact assumptions, constant compatibility
requirements, and consequence ledger needed to state:

    if GlobalConcavityOfPsi1, SecondaryPeakExclusion, and
    TransportCommutatorDominationForVBarrier hold with compatible constants,
    then the monitored symmetric Hou-Luo route has conditional regularity and
    a finite BKM monitor.

The emitter is fail-closed: unconditional global axial monotonicity, a full
Clay Navier-Stokes solution, and Clay promotion are all explicitly false.
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


CONTRACT = "ns_sprint140_conditional_barrier_assembly"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint140_conditional_barrier_assembly")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"

SPRINT = 140
AFTER_SPRINT = 139
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
ROUTE = "SymmetricHouLuoMonitoredRoute"
THEOREM_INTERFACE = "ConditionalSymmetricHouLuoRouteRegularityBKMFinite"
ROUTE_DECISION = "assemble_conditional_interface_fail_closed"
PROMOTION_DECISION = "hold_no_clay_promotion"

GLOBAL_CONCAVITY = "GlobalConcavityOfPsi1"
SECONDARY_PEAK_EXCLUSION = "SecondaryPeakExclusion"
COMMUTATOR_DOMINATION = "TransportCommutatorDominationForVBarrier"
CONSTANT_COMPATIBILITY = "CompatibleBarrierConstants"
MONITORED_REGULARITY = "ConditionalMonitoredRouteRegularity"
BKM_FINITE = "ConditionalBKMFiniteForSymmetricHouLuoRoute"
GUARD = "ConditionalNotFullClayGuard"

REQUIRED_ROW_IDS = {
    GLOBAL_CONCAVITY,
    SECONDARY_PEAK_EXCLUSION,
    COMMUTATOR_DOMINATION,
    CONSTANT_COMPATIBILITY,
    MONITORED_REGULARITY,
    BKM_FINITE,
    GUARD,
}

SOURCE_ARTIFACTS = {
    "route_fork_classifier": (
        "outputs/ns_sprint139_barrier_route_fork_classifier/"
        "ns_sprint139_barrier_route_fork_classifier_summary.json"
    ),
    "commutator_sign_route": (
        "outputs/ns_sprint139_commutator_sign_route/"
        "ns_sprint139_commutator_sign_route_summary.json"
    ),
    "localized_kernel_sign_sampler": (
        "outputs/ns_sprint139_localized_kernel_sign_sampler/"
        "ns_sprint139_localized_kernel_sign_sampler_summary.json"
    ),
}

V_BARRIER_EQUATION = (
    "D_t v = nu Ltilde v + 2 v partial_z psi1 + 2 u1 partial_z^2 psi1 "
    "- (partial_z u^r) partial_r u1 - (partial_z u^z) v"
)
BKM_MONITOR = (
    "integral_0^T ||omega(t)||_{L_infinity} dt along "
    "SymmetricHouLuoMonitoredRoute"
)


@dataclass(frozen=True)
class AssemblyRow:
    row_id: str
    layer: str
    role: str
    statement: str
    dependency_ids: tuple[str, ...]
    constant_requirements: tuple[str, ...]
    consequence: str
    status: str
    assumption_required: bool
    assumption_proved_here: bool
    constants_compatible_required: bool
    constants_compatible_proved_here: bool
    conditional_route_regular: bool
    bkm_finite_conditional: bool
    unconditional_global_axial_monotonicity: bool
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool
    conditional_not_full_clay: bool

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row["dependency_ids"] = list(self.dependency_ids)
        row["constant_requirements"] = list(self.constant_requirements)
        row["assumption_id"] = self.row_id
        row["assumption_name"] = self.row_id
        row["missing_input"] = (
            []
            if self.row_id == GUARD
            else [
                "compatible constants required but absent/not proved here",
                "analytic assumption input remains external to this emitter",
            ]
        )
        row["compatibility_inputs_absent"] = not self.constants_compatible_proved_here
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
        AssemblyRow(
            row_id=GLOBAL_CONCAVITY,
            layer="assumption",
            role="barrier_source_sign",
            statement=(
                "Assume partial_z^2 psi1 supplies the global sign or dominance "
                "margin needed by the v-barrier at every admissible first "
                "positive maximum on the symmetric Hou-Luo monitored route."
            ),
            dependency_ids=(),
            constant_requirements=(
                "concavity_margin kappa_psi > 0",
                "valid on the complete monitored crossing set",
                "boundary and annular source compatibility",
            ),
            consequence=(
                "The source term 2 u1 partial_z^2 psi1 contributes a favorable "
                "or dominated term in the conditional barrier ledger."
            ),
            status="assumed_not_proved",
            assumption_required=True,
            assumption_proved_here=False,
            constants_compatible_required=True,
            constants_compatible_proved_here=False,
            conditional_route_regular=False,
            bkm_finite_conditional=False,
            unconditional_global_axial_monotonicity=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            conditional_not_full_clay=True,
        ),
        AssemblyRow(
            row_id=SECONDARY_PEAK_EXCLUSION,
            layer="assumption",
            role="crossing_set_control",
            statement=(
                "Assume no secondary axial peak, shoulder, or off-route "
                "positive local maximum of v forms outside the primary "
                "barrier region during the monitored time interval."
            ),
            dependency_ids=(),
            constant_requirements=(
                "single monitored crossing region remains exhaustive",
                "shape persistence time window covers the route interval",
                "axis and boundary crossing exclusions share the same scale",
            ),
            consequence=(
                "The maximum-principle contradiction only needs to be checked "
                "on the primary symmetric Hou-Luo barrier route."
            ),
            status="assumed_not_proved",
            assumption_required=True,
            assumption_proved_here=False,
            constants_compatible_required=True,
            constants_compatible_proved_here=False,
            conditional_route_regular=False,
            bkm_finite_conditional=False,
            unconditional_global_axial_monotonicity=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            conditional_not_full_clay=True,
        ),
        AssemblyRow(
            row_id=COMMUTATOR_DOMINATION,
            layer="assumption",
            role="transport_commutator_budget",
            statement=(
                "Assume the positive part of -(partial_z u^r) partial_r u1 "
                "is dominated by the available v-barrier margin at every "
                "admissible first positive maximum, with any Biot-Savart "
                "logarithmic loss included in the constants."
            ),
            dependency_ids=(),
            constant_requirements=(
                "commutator_margin kappa_comm > 0",
                "log-aware strain factor absorbed by the route budget",
                "radial-gradient coupling controlled on the crossing set",
            ),
            consequence=(
                "The nonhomogeneous radial commutator cannot create the first "
                "positive v crossing under the conditional ledger."
            ),
            status="assumed_not_proved",
            assumption_required=True,
            assumption_proved_here=False,
            constants_compatible_required=True,
            constants_compatible_proved_here=False,
            conditional_route_regular=False,
            bkm_finite_conditional=False,
            unconditional_global_axial_monotonicity=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            conditional_not_full_clay=True,
        ),
        AssemblyRow(
            row_id=CONSTANT_COMPATIBILITY,
            layer="interface",
            role="constant_budget",
            statement=(
                "Require one compatible constant ledger linking concavity, "
                "secondary-peak exclusion, commutator domination, viscosity, "
                "route localization, and BKM monitor bounds."
            ),
            dependency_ids=(
                GLOBAL_CONCAVITY,
                SECONDARY_PEAK_EXCLUSION,
                COMMUTATOR_DOMINATION,
            ),
            constant_requirements=(
                "kappa_psi - kappa_comm - kappa_shape_loss > 0",
                "localization radius and time window shared by all assumptions",
                "BKM monitor constant finite under the same route parameters",
                "no assumption uses constants outside the symmetric route class",
            ),
            consequence=(
                "The three assumptions can be composed into a single "
                "conditional theorem interface only when their constants are "
                "jointly satisfiable."
            ),
            status="required_interface_check_not_proved",
            assumption_required=True,
            assumption_proved_here=False,
            constants_compatible_required=True,
            constants_compatible_proved_here=False,
            conditional_route_regular=False,
            bkm_finite_conditional=False,
            unconditional_global_axial_monotonicity=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            conditional_not_full_clay=True,
        ),
        AssemblyRow(
            row_id=MONITORED_REGULARITY,
            layer="conditional_consequence",
            role="route_regularness",
            statement=(
                "If the three analytic assumptions and the compatible constant "
                "ledger hold, then v cannot achieve a first positive crossing "
                "on the symmetric Hou-Luo monitored route, so the monitored "
                "barrier regularity statement holds conditionally."
            ),
            dependency_ids=(
                GLOBAL_CONCAVITY,
                SECONDARY_PEAK_EXCLUSION,
                COMMUTATOR_DOMINATION,
                CONSTANT_COMPATIBILITY,
            ),
            constant_requirements=(
                "strict positive residual barrier margin",
                "route-local parabolic regularity constants finite",
                "maximum-principle boundary leakage excluded by assumptions",
            ),
            consequence=(
                "Conditional monitored-route regularity is available as an "
                "interface theorem, not as an unconditional global theorem."
            ),
            status="conditional_if_assumptions",
            assumption_required=False,
            assumption_proved_here=False,
            constants_compatible_required=True,
            constants_compatible_proved_here=False,
            conditional_route_regular=True,
            bkm_finite_conditional=False,
            unconditional_global_axial_monotonicity=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            conditional_not_full_clay=True,
        ),
        AssemblyRow(
            row_id=BKM_FINITE,
            layer="conditional_consequence",
            role="bkm_monitor",
            statement=(
                "Under the same conditional route regularity hypotheses, the "
                "symmetric Hou-Luo monitored-route Beale-Kato-Majda integral "
                "is finite on the monitored interval."
            ),
            dependency_ids=(
                MONITORED_REGULARITY,
                CONSTANT_COMPATIBILITY,
            ),
            constant_requirements=(
                "finite monitored vorticity envelope M_omega(T)",
                "BKM integral bound T * M_omega(T) or sharper route envelope",
                "monitor applies only to the symmetric Hou-Luo route interval",
            ),
            consequence=(
                "BKM finite is emitted only as a conditional monitored-route "
                "consequence and does not solve the full Clay problem."
            ),
            status="conditional_if_assumptions",
            assumption_required=False,
            assumption_proved_here=False,
            constants_compatible_required=True,
            constants_compatible_proved_here=False,
            conditional_route_regular=True,
            bkm_finite_conditional=True,
            unconditional_global_axial_monotonicity=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            conditional_not_full_clay=True,
        ),
        AssemblyRow(
            row_id=GUARD,
            layer="guard",
            role="promotion_blocker",
            statement=(
                "The assembled theorem is conditional and route-local. It is "
                "not unconditional global axial monotonicity and is not a full "
                "Clay Navier-Stokes solution or promotion."
            ),
            dependency_ids=(
                MONITORED_REGULARITY,
                BKM_FINITE,
            ),
            constant_requirements=(
                "all assumptions remain explicit in exported theorem surface",
                "no row may set unconditional_global_axial_monotonicity true",
                "no row may set full_clay_ns_solved or clay_navier_stokes_promoted true",
            ),
            consequence=(
                "Downstream consumers can import the conditional interface "
                "without interpreting it as a Clay-level theorem."
            ),
            status="fail_closed_guard",
            assumption_required=False,
            assumption_proved_here=False,
            constants_compatible_required=False,
            constants_compatible_proved_here=False,
            conditional_route_regular=True,
            bkm_finite_conditional=True,
            unconditional_global_axial_monotonicity=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            conditional_not_full_clay=True,
        ),
    ]
    return [row.as_row() for row in rows]


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = (
        "row_id",
        "layer",
        "role",
        "statement",
        "dependency_ids",
        "constant_requirements",
        "assumption_id",
        "assumption_name",
        "missing_input",
        "compatibility_inputs_absent",
        "consequence",
        "status",
        "assumption_required",
        "assumption_proved_here",
        "constants_compatible_required",
        "constants_compatible_proved_here",
        "conditional_route_regular",
        "bkm_finite_conditional",
        "unconditional_global_axial_monotonicity",
        "full_clay_ns_solved",
        "clay_navier_stokes_promoted",
        "conditional_not_full_clay",
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
            serializable["dependency_ids"] = "; ".join(serializable["dependency_ids"])
            serializable["constant_requirements"] = "; ".join(
                serializable["constant_requirements"]
            )
            serializable["missing_input"] = "; ".join(serializable["missing_input"])
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

    assumptions = [GLOBAL_CONCAVITY, SECONDARY_PEAK_EXCLUSION, COMMUTATOR_DOMINATION]
    consequences = [MONITORED_REGULARITY, BKM_FINITE]
    invariant_failures: list[str] = []

    if missing_required:
        invariant_failures.append("missing_required_rows:" + ",".join(missing_required))
    for assumption in assumptions:
        row = row_by_id.get(assumption, {})
        if not row.get("assumption_required"):
            invariant_failures.append("assumption_not_required:" + assumption)
        if row.get("assumption_proved_here"):
            invariant_failures.append("assumption_proved_here:" + assumption)
    if not row_by_id.get(CONSTANT_COMPATIBILITY, {}).get("constants_compatible_required"):
        invariant_failures.append("constants_compatibility_not_required")
    if row_by_id.get(CONSTANT_COMPATIBILITY, {}).get("constants_compatible_proved_here"):
        invariant_failures.append("constants_compatibility_proved_here")
    if not row_by_id.get(MONITORED_REGULARITY, {}).get("conditional_route_regular"):
        invariant_failures.append("conditional_route_regular_missing")
    if not row_by_id.get(BKM_FINITE, {}).get("bkm_finite_conditional"):
        invariant_failures.append("conditional_bkm_finite_missing")
    if any(row["unconditional_global_axial_monotonicity"] for row in rows):
        invariant_failures.append("unconditional_global_axial_monotonicity_detected")
    if any(row["full_clay_ns_solved"] for row in rows):
        invariant_failures.append("full_clay_ns_solved_detected")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        invariant_failures.append("clay_promotion_detected")
    if not all(row["conditional_not_full_clay"] for row in rows):
        invariant_failures.append("conditional_not_full_clay_not_global")
    if any(row["claim_closed"] or row["claim_proved"] or row["claim_proven"] for row in rows):
        invariant_failures.append("unconditional_claim_closure_detected")

    assumptions_explicit = sorted(
        row["row_id"]
        for row in rows
        if row["row_id"] in assumptions and row["assumption_required"]
    )
    invariants_passed = not invariant_failures

    return {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "after_sprint": AFTER_SPRINT,
        "program": PROGRAM,
        "route": ROUTE,
        "theorem_interface": THEOREM_INTERFACE,
        "row_count": len(rows),
        "assumptions": assumptions,
        "assumptions_explicit": assumptions_explicit,
        "constants_interface": CONSTANT_COMPATIBILITY,
        "constants_compatible": "required_not_proved_here",
        "constants_compatible_required": True,
        "constants_compatible_proved_here": False,
        "conditional_consequences": consequences,
        "conditional_monitored_route_regular": True,
        "conditional_bkm_finite": True,
        "bkm_monitor": BKM_MONITOR,
        "v_barrier_equation": V_BARRIER_EQUATION,
        "route_decision": ROUTE_DECISION,
        "decision": "conditional_interface_assembled_fail_closed",
        "promotion_decision": PROMOTION_DECISION,
        "unconditional_global_axial_monotonicity": False,
        "global_proof": False,
        "global_proof_closed": False,
        "unconditional_proof": False,
        "global_axial_monotonicity_proved": False,
        "global_axial_monotonicity_proven": False,
        "global_barrier_closed": False,
        "proof_claimed": False,
        "proof_closed": False,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "clay_promoted": False,
        "promotion_allowed": False,
        "conditional_not_full_clay": True,
        "source_artifacts": SOURCE_ARTIFACTS,
        "source_summary_hashes": source_hashes,
        "row_hashes": row_hashes,
        "rows_hash": rows_hash,
        "summary_payload_hash_without_self": stable_hash(
            {
                "contract": CONTRACT,
                "theorem_interface": THEOREM_INTERFACE,
                "assumptions": assumptions,
                "conditional_consequences": consequences,
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
                "Worker 2 owns only scripts/ns_sprint140_conditional_barrier_assembly.py "
                "and outputs/ns_sprint140_conditional_barrier_assembly/."
            ),
            "R": (
                "Assemble the conditional theorem interface from "
                "GlobalConcavityOfPsi1, SecondaryPeakExclusion, "
                "TransportCommutatorDominationForVBarrier, and compatible constants."
            ),
            "C": (
                "Deterministic stdlib Python emitter with dataclass rows, stable "
                "SHA-256 hashes, invariant validation, JSON, CSV, and Markdown."
            ),
            "S": (
                "The symmetric Hou-Luo monitored route has conditional regularity "
                "and conditional finite BKM only if the assumptions and constants hold."
            ),
            "L": (
                "Sprint 139 route ledgers -> explicit assumptions -> compatible "
                "constant interface -> conditional route regularity -> conditional BKM."
            ),
            "P": (
                "Use as a conditional interface artifact for downstream formalization, "
                "not as an unconditional Navier-Stokes proof."
            ),
            "G": (
                "Validation passes only when unconditional_global_axial_monotonicity, "
                "full_clay_ns_solved, and clay_navier_stokes_promoted are false, "
                "while conditional_not_full_clay is true."
            ),
            "F": (
                "Missing assumptions, hidden proved assumptions, incompatible constant "
                "surface, unconditional axial monotonicity, Clay solution, or Clay "
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
    if summary["sprint"] != SPRINT or summary["after_sprint"] != AFTER_SPRINT:
        raise ValueError("wrong sprint metadata")
    if summary["route_decision"] != ROUTE_DECISION:
        raise ValueError("wrong route decision")
    if summary["assumptions"] != [
        GLOBAL_CONCAVITY,
        SECONDARY_PEAK_EXCLUSION,
        COMMUTATOR_DOMINATION,
    ]:
        raise ValueError("wrong assumption interface")
    if summary["constants_compatible"] != "required_not_proved_here":
        raise ValueError("constant compatibility must remain required, not proved")
    if not summary["conditional_monitored_route_regular"]:
        raise ValueError("conditional monitored-route regularity must be emitted")
    if not summary["conditional_bkm_finite"]:
        raise ValueError("conditional BKM finite must be emitted")
    if summary["unconditional_global_axial_monotonicity"]:
        raise ValueError("unconditional global axial monotonicity is forbidden")
    if summary["global_axial_monotonicity_proved"] or summary["global_axial_monotonicity_proven"]:
        raise ValueError("global axial monotonicity must not be proved")
    if summary["global_barrier_closed"] or summary["proof_claimed"] or summary["proof_closed"]:
        raise ValueError("unconditional proof closure is forbidden")
    if summary["full_clay_ns_solved"]:
        raise ValueError("full Clay NS must remain unsolved")
    if summary["clay_navier_stokes_promoted"] or summary["clay_promoted"]:
        raise ValueError("Clay promotion is forbidden")
    if summary["promotion_allowed"]:
        raise ValueError("promotion must not be allowed")
    if not summary["conditional_not_full_clay"]:
        raise ValueError("conditional_not_full_clay must be true")
    if any(row["unconditional_global_axial_monotonicity"] for row in rows):
        raise ValueError("row claims unconditional global axial monotonicity")
    if any(row["full_clay_ns_solved"] for row in rows):
        raise ValueError("row claims full Clay NS solved")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        raise ValueError("row promotes Clay Navier-Stokes")
    if not all(row["conditional_not_full_clay"] for row in rows):
        raise ValueError("row failed conditional_not_full_clay guard")
    if len({row["row_hash"] for row in rows}) != len(rows):
        raise ValueError("row hashes must be unique")
    if summary["invariant_failures"]:
        raise ValueError("; ".join(summary["invariant_failures"]))


def build_report(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 140 Conditional Barrier Assembly",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Sprint: `{summary['sprint']}` after Sprint `{summary['after_sprint']}`",
        f"- Route: `{summary['route']}`",
        f"- Theorem interface: `{summary['theorem_interface']}`",
        f"- Decision: `{summary['decision']}`",
        f"- Conditional monitored-route regularity: `{str(summary['conditional_monitored_route_regular']).lower()}`",
        f"- Conditional BKM finite: `{str(summary['conditional_bkm_finite']).lower()}`",
        f"- Unconditional global axial monotonicity: `{str(summary['unconditional_global_axial_monotonicity']).lower()}`",
        f"- Full Clay NS solved: `{str(summary['full_clay_ns_solved']).lower()}`",
        f"- Clay Navier-Stokes promoted: `{str(summary['clay_navier_stokes_promoted']).lower()}`",
        f"- Conditional not full Clay: `{str(summary['conditional_not_full_clay']).lower()}`",
        f"- Rows hash: `{summary['rows_hash']}`",
        "",
        "## Assumptions",
        "",
    ]
    for assumption in summary["assumptions"]:
        lines.append(f"- `{assumption}`")
    lines.extend(
        [
            "- `compatible constants` via `CompatibleBarrierConstants`",
            "",
            "## Barrier Equation",
            "",
            f"- `{summary['v_barrier_equation']}`",
            "",
            "## Rows",
            "",
            "| Row | Layer | Status | Role | Statement | Consequence | Row Hash |",
            "| --- | --- | --- | --- | --- | --- | --- |",
        ]
    )
    for row in rows:
        statement = row["statement"].replace("|", "\\|")
        consequence = row["consequence"].replace("|", "\\|")
        lines.append(
            f"| `{row['row_id']}` | `{row['layer']}` | `{row['status']}` | "
            f"`{row['role']}` | {statement} | {consequence} | `{row['row_hash']}` |"
        )
    lines.extend(
        [
            "",
            "## Source Summary Hashes",
            "",
        ]
    )
    for key, digest in summary["source_summary_hashes"].items():
        lines.append(f"- {key}: `{digest}`")
    lines.extend(
        [
            "",
            "## Guard",
            "",
            (
                "This artifact is a conditional monitored-route interface. It "
                "keeps unconditional global axial monotonicity false, full "
                "Clay Navier-Stokes solved false, Clay promotion false, and "
                "conditional_not_full_clay true."
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
                "conditional_bkm_finite": summary["conditional_bkm_finite"],
                "conditional_monitored_route_regular": summary[
                    "conditional_monitored_route_regular"
                ],
                "conditional_not_full_clay": summary["conditional_not_full_clay"],
                "contract": summary["contract"],
                "exit_code": summary["exit_code"],
                "full_clay_ns_solved": summary["full_clay_ns_solved"],
                "rows_hash": summary["rows_hash"],
                "unconditional_global_axial_monotonicity": summary[
                    "unconditional_global_axial_monotonicity"
                ],
            },
            sort_keys=True,
        )
    )
    return int(summary["exit_code"])


if __name__ == "__main__":
    sys.exit(main())
