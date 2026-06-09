#!/usr/bin/env python3
"""Sprint 140 NS constant compatibility ledger.

This deterministic emitter records the constant-compatibility inputs needed
to assemble the conditional Hou-Luo-style axial barrier route across:

* concavity margin,
* secondary peak exclusion radius/window,
* commutator domination margin/log loss, and
* diffusion/strain budget.

It is a compatibility ledger, not a proof.  Required constants are named,
absent inputs are kept explicit, and the assembly remains conditional and
fail-closed.  No full Clay Navier-Stokes promotion is emitted.
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


CONTRACT = "ns_sprint140_constant_compatibility_ledger"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint140_constant_compatibility_ledger")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"

SPRINT = 140
AFTER_SPRINT = 139
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
PARENT_ROUTE = "ConditionalRegularityAssembly"
ROUTE_DECISION = "constant_compatibility_conditional_fail_closed"
PROMOTION_DECISION = "hold_no_clay_promotion"

CONCAVITY = "concavity_margin"
SECONDARY_PEAK = "secondary_peak_exclusion_radius_window"
COMMUTATOR = "commutator_domination_margin_log_loss"
DIFFUSION_STRAIN = "diffusion_strain_budget"
ASSEMBLY = "conditional_assembly_compatibility"

REQUIRED_ROW_IDS = {
    CONCAVITY,
    SECONDARY_PEAK,
    COMMUTATOR,
    DIFFUSION_STRAIN,
    ASSEMBLY,
}

SOURCE_ARTIFACTS = {
    "sprint138_global_concavity": "outputs/ns_sprint138_global_concavity_blocker/ns_sprint138_global_concavity_blocker_summary.json",
    "sprint138_secondary_peak": "outputs/ns_sprint138_secondary_peak_exclusion/ns_sprint138_secondary_peak_exclusion_summary.json",
    "sprint138_transport_commutator": "outputs/ns_sprint138_transport_commutator_budget/ns_sprint138_transport_commutator_budget_summary.json",
    "sprint139_route_fork": "outputs/ns_sprint139_barrier_route_fork_classifier/ns_sprint139_barrier_route_fork_classifier_summary.json",
    "sprint139_commutator_sign": "outputs/ns_sprint139_commutator_sign_route/ns_sprint139_commutator_sign_route_summary.json",
}


@dataclass(frozen=True)
class CompatibilityRow:
    row_id: str
    assumption_group: str
    compatibility_role: str
    required_inputs: tuple[str, ...]
    present_inputs: tuple[str, ...]
    absent_inputs: tuple[str, ...]
    compatibility_condition: str
    incompatibility_risk: str
    fail_closed_reason: str
    source_routes: tuple[str, ...]
    input_status: str
    constants_available: bool
    compatibility_closed: bool
    conditional_only: bool
    proof_closed: bool
    global_barrier_closed: bool
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool
    promotion_allowed: bool

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        for key in ("required_inputs", "present_inputs", "absent_inputs", "source_routes"):
            row[key] = list(row[key])
        row["assumption_id"] = self.assumption_group
        row["assumption_name"] = self.assumption_group
        row["missing_input"] = list(row["absent_inputs"])
        row["blocked_claim"] = row["compatibility_condition"]
        row["claim_closed"] = self.compatibility_closed
        row["claim_proved"] = self.proof_closed
        row["claim_proven"] = self.proof_closed
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
        CompatibilityRow(
            row_id=CONCAVITY,
            assumption_group="GlobalConcavityOfPsi1",
            compatibility_role="supply_favorable_source_margin",
            required_inputs=(
                "strict concavity or dominance constant kappa_concavity > 0",
                "scale/window over which partial_z^2 psi1 has the required sign",
                "lower bound matching u1 amplitude at every first v crossing",
                "boundary and annular compatibility for the nonlocal psi1 kernel",
            ),
            present_inputs=(
                "local center-sign heuristic recorded by Sprint 138",
                "named global concavity blocker and route fork",
            ),
            absent_inputs=(
                "global kappa_concavity constant",
                "proof that the margin holds at all primary and secondary crossing points",
                "nonlocal boundary/annulus sign theorem",
                "time persistence of the margin through the barrier window",
            ),
            compatibility_condition=(
                "The favorable concavity margin must be positive on the same "
                "space-time crossing set used by peak exclusion and commutator "
                "domination."
            ),
            incompatibility_risk=(
                "A local concavity margin can be irrelevant if the first "
                "positive v crossing occurs off-center, outside the radius, or "
                "after the margin window expires."
            ),
            fail_closed_reason=(
                "The ledger has no global kappa_concavity, no universal crossing "
                "set theorem, and no persistence proof."
            ),
            source_routes=(
                "ns_sprint138_global_concavity_blocker",
                "ns_sprint139_barrier_route_fork_classifier",
            ),
            input_status="required_absent",
            constants_available=False,
            compatibility_closed=False,
            conditional_only=True,
            proof_closed=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        CompatibilityRow(
            row_id=SECONDARY_PEAK,
            assumption_group="SecondaryPeakExclusion",
            compatibility_role="align_crossing_set_radius_and_time_window",
            required_inputs=(
                "exclusion radius R_excl covering every off-primary positive maximum",
                "time window T_excl matching the concavity and commutator windows",
                "zero-count or shape-persistence theorem for v=partial_z u1",
                "axis, boundary, and annular leakage controls for the excluded region",
            ),
            present_inputs=(
                "single-peak initial shape recorded as conditional input",
                "secondary peak obstruction row from Sprint 138",
            ),
            absent_inputs=(
                "scale-uniform R_excl",
                "scale-uniform T_excl",
                "proof no shoulder or secondary maximum forms",
                "compatibility proof that all first crossings lie inside the concavity margin region",
            ),
            compatibility_condition=(
                "The exclusion radius/window must cover exactly the first-crossing "
                "locations where concavity and commutator constants are invoked."
            ),
            incompatibility_risk=(
                "If R_excl or T_excl is narrower than the commutator or "
                "concavity domain, the conditional assembly can silently use "
                "constants at points not covered by peak exclusion."
            ),
            fail_closed_reason=(
                "The ledger has no persistent exclusion radius/window and no "
                "zero-count theorem for the coupled axisymmetric system."
            ),
            source_routes=(
                "ns_sprint138_secondary_peak_exclusion",
                "ns_sprint139_barrier_route_fork_classifier",
            ),
            input_status="required_absent",
            constants_available=False,
            compatibility_closed=False,
            conditional_only=True,
            proof_closed=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        CompatibilityRow(
            row_id=COMMUTATOR,
            assumption_group="TransportCommutatorDomination",
            compatibility_role="absorb_positive_radial_commutator_with_log_loss",
            required_inputs=(
                "strict domination margin kappa_comm > 0 for max(-(partial_z u^r) partial_r u1, 0)",
                "explicit Biot-Savart log-loss exponent or cancellation theorem",
                "scale relation between kappa_comm and kappa_concavity",
                "radial-gradient control for partial_r u1 on the active crossing set",
            ),
            present_inputs=(
                "commutator term isolated in Sprint 138 and Sprint 139",
                "pointwise and weighted domination hypotheses named",
            ),
            absent_inputs=(
                "pointwise favorable sign theorem",
                "quantitative kappa_comm margin",
                "log-aware domination inequality",
                "radial-gradient coupling bound compatible with diffusion and strain",
            ),
            compatibility_condition=(
                "The positive commutator source, including any Biot-Savart "
                "log loss, must be strictly dominated by the same margin budget "
                "available from concavity, diffusion, and strain controls."
            ),
            incompatibility_risk=(
                "A logarithmic strain loss can exceed a polynomial or local "
                "margin unless the constants include the loss explicitly."
            ),
            fail_closed_reason=(
                "The ledger names the domination theorem but records no sign, "
                "no margin, no log cancellation, and no radial-gradient bound."
            ),
            source_routes=(
                "ns_sprint138_transport_commutator_budget",
                "ns_sprint139_commutator_sign_route",
                "ns_sprint139_barrier_route_fork_classifier",
            ),
            input_status="required_absent",
            constants_available=False,
            compatibility_closed=False,
            conditional_only=True,
            proof_closed=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        CompatibilityRow(
            row_id=DIFFUSION_STRAIN,
            assumption_group="DiffusionStrainBudget",
            compatibility_role="close_total_maximum_principle_budget",
            required_inputs=(
                "diffusion lower or sign budget at first positive v maximum",
                "strain coefficient upper budget for terms proportional to v",
                "time-integrable strain bound with any log loss included",
                "strict residual margin after concavity, commutator, diffusion, and strain are combined",
            ),
            present_inputs=(
                "first-positive-maximum geometry recorded by Sprint 139",
                "diffusion and strain terms identified in the v-barrier equation",
            ),
            absent_inputs=(
                "closed diffusion sign budget with constants",
                "closed strain budget with time integral",
                "combined residual margin after log losses",
                "operator boundary leakage estimate for the chosen barrier window",
            ),
            compatibility_condition=(
                "After all source, commutator, diffusion, and strain terms are "
                "put on the same scale, the residual maximum-principle budget "
                "must remain strictly favorable."
            ),
            incompatibility_risk=(
                "The individual conditional assumptions can be too weak in "
                "aggregate if diffusion gives no usable margin or strain/log "
                "terms consume the entire concavity budget."
            ),
            fail_closed_reason=(
                "No combined strict residual budget is available, and no "
                "scale-uniform strain/log accounting has been supplied."
            ),
            source_routes=(
                "ns_sprint138_transport_commutator_budget",
                "ns_sprint139_commutator_sign_route",
            ),
            input_status="required_absent",
            constants_available=False,
            compatibility_closed=False,
            conditional_only=True,
            proof_closed=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        CompatibilityRow(
            row_id=ASSEMBLY,
            assumption_group="ConditionalRegularityAssembly",
            compatibility_role="require_all_constants_simultaneously",
            required_inputs=(
                "kappa_concavity, R_excl, T_excl, kappa_comm, log-loss budget, diffusion budget, and strain budget",
                "single crossing set shared by all assumptions",
                "strict inequality showing total favorable margin exceeds all adverse terms",
                "route-to-global regularity bridge separated from Clay promotion",
            ),
            present_inputs=(
                "ranked conditional assembly route from Sprint 139",
                "named fail-closed blockers for each analytic gate",
            ),
            absent_inputs=(
                "simultaneous satisfiability proof for all constants",
                "cross-window compatibility proof",
                "strict combined inequality with numerical or symbolic constants",
                "full Navier-Stokes Clay-class promotion theorem",
            ),
            compatibility_condition=(
                "The assembly can only be stated conditionally: if all named "
                "margins, radii, windows, log-loss, diffusion, and strain "
                "budgets are supplied on one common crossing set, then the "
                "route-level barrier may be attempted."
            ),
            incompatibility_risk=(
                "The assumptions may be mutually inconsistent or may apply to "
                "different radii, time windows, or crossing sets."
            ),
            fail_closed_reason=(
                "At least one required input is absent in every analytic row, "
                "and the ledger records no simultaneous constant proof."
            ),
            source_routes=(
                "ns_sprint139_barrier_route_fork_classifier",
                "ns_sprint139_commutator_sign_route",
            ),
            input_status="conditional_fail_closed",
            constants_available=False,
            compatibility_closed=False,
            conditional_only=True,
            proof_closed=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
    ]
    return [row.as_row() for row in rows]


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = (
        "row_id",
        "assumption_group",
        "assumption_id",
        "assumption_name",
        "compatibility_role",
        "required_inputs",
        "present_inputs",
        "absent_inputs",
        "compatibility_condition",
        "incompatibility_risk",
        "fail_closed_reason",
        "source_routes",
        "input_status",
        "constants_available",
        "compatibility_closed",
        "conditional_only",
        "proof_closed",
        "global_barrier_closed",
        "full_clay_ns_solved",
        "clay_navier_stokes_promoted",
        "promotion_allowed",
        "missing_input",
        "blocked_claim",
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
                "required_inputs",
                "present_inputs",
                "absent_inputs",
                "source_routes",
                "missing_input",
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
    absent_by_row = {row["row_id"]: row["absent_inputs"] for row in rows}
    required_by_row = {row["row_id"]: row["required_inputs"] for row in rows}

    invariant_failures: list[str] = []
    if missing_required:
        invariant_failures.append("missing_required_rows:" + ",".join(missing_required))
    if any(row["constants_available"] for row in rows):
        invariant_failures.append("constants_incorrectly_available")
    if any(row["compatibility_closed"] for row in rows):
        invariant_failures.append("compatibility_incorrectly_closed")
    if not all(row["conditional_only"] for row in rows):
        invariant_failures.append("nonconditional_row_detected")
    if any(row["proof_closed"] for row in rows):
        invariant_failures.append("proof_closure_detected")
    if any(row["global_barrier_closed"] for row in rows):
        invariant_failures.append("global_barrier_closure_detected")
    if any(row["full_clay_ns_solved"] for row in rows):
        invariant_failures.append("full_clay_ns_solved_detected")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        invariant_failures.append("clay_promotion_detected")
    if any(row["promotion_allowed"] for row in rows):
        invariant_failures.append("promotion_allowed_detected")
    if not all(row["absent_inputs"] for row in rows):
        invariant_failures.append("row_without_absent_inputs")
    if "log" not in " ".join(row_by_id.get(COMMUTATOR, {}).get("required_inputs", [])).lower():
        invariant_failures.append("commutator_log_loss_not_required")
    if "diffusion" not in row_by_id.get(DIFFUSION_STRAIN, {}).get("assumption_group", "").lower():
        invariant_failures.append("diffusion_strain_row_missing")
    if row_by_id.get(ASSEMBLY, {}).get("input_status") != "conditional_fail_closed":
        invariant_failures.append("assembly_not_fail_closed")

    invariants_passed = not invariant_failures

    return {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "after_sprint": AFTER_SPRINT,
        "program": PROGRAM,
        "parent_route": PARENT_ROUTE,
        "row_count": len(rows),
        "required_row_ids": sorted(REQUIRED_ROW_IDS),
        "route_decision": ROUTE_DECISION,
        "promotion_decision": PROMOTION_DECISION,
        "artifact_complete": invariants_passed,
        "fail_closed": True,
        "conditional_assembly_only": True,
        "assembly_remains_conditional": True,
        "constant_compatibility_closed": False,
        "compatibility_inputs_required": required_by_row,
        "compatibility_inputs_absent": absent_by_row,
        "all_rows_have_absent_inputs": all(row["absent_inputs"] for row in rows),
        "constants_available": False,
        "global_barrier_closed": False,
        "global_proof": False,
        "global_proof_closed": False,
        "unconditional_proof": False,
        "proof_claimed": False,
        "proof_closed": False,
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
                "required_row_ids": sorted(REQUIRED_ROW_IDS),
                "compatibility_inputs_absent": absent_by_row,
                "row_hashes": row_hashes,
                "rows_hash": rows_hash,
            }
        ),
        "invariant_failures": invariant_failures,
        "invariants_passed": invariants_passed,
        "exit_code": 0 if invariants_passed else 1,
        "control_card": {
            "O": (
                "Worker 3 owns only scripts/ns_sprint140_constant_compatibility_ledger.py "
                "and outputs/ns_sprint140_constant_compatibility_ledger/."
            ),
            "R": (
                "Emit a deterministic ledger for constant compatibility across "
                "concavity margin, secondary peak exclusion radius/window, "
                "commutator domination margin/log loss, and diffusion/strain budget."
            ),
            "C": (
                "Stdlib Python emitter with dataclass rows, stable SHA-256 "
                "hashes, validation, JSON, CSV, and Markdown outputs."
            ),
            "S": (
                "Every analytic compatibility input is required but absent; "
                "the assembly remains conditional and fail-closed."
            ),
            "L": (
                "Sprint 138/139 blockers -> constant requirements -> absent "
                "inputs -> conditional assembly only -> no promotion."
            ),
            "P": (
                "Use this ledger to state the assumptions needed for a future "
                "conditional route assembly, not as a regularity proof."
            ),
            "G": (
                "Validation passes only when constants are unavailable, "
                "compatibility/proof/global barrier closure are false, and "
                "Clay promotion is false."
            ),
            "F": (
                "Missing rows, absent-input omissions, hidden constant closure, "
                "global barrier closure, proof closure, or promotion fails validation."
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
    if not summary["fail_closed"] or not summary["assembly_remains_conditional"]:
        raise ValueError("ledger must remain fail-closed and conditional")
    if summary["constant_compatibility_closed"]:
        raise ValueError("constant compatibility must not close")
    for forbidden in (
        "constants_available",
        "global_barrier_closed",
        "proof_claimed",
        "proof_closed",
        "full_clay_ns_solved",
        "clay_navier_stokes_promoted",
        "clay_promoted",
        "promotion_allowed",
    ):
        if summary[forbidden]:
            raise ValueError("forbidden summary flag is true: " + forbidden)
    if summary["invariant_failures"]:
        raise ValueError("invariant failures: " + "; ".join(summary["invariant_failures"]))
    if any(not row["absent_inputs"] for row in rows):
        raise ValueError("each compatibility row must record absent inputs")
    for row in rows:
        if row["constants_available"] or row["compatibility_closed"] or row["proof_closed"]:
            raise ValueError("row incorrectly closes compatibility: " + row["row_id"])
        if row["global_barrier_closed"] or row["full_clay_ns_solved"]:
            raise ValueError("row incorrectly closes global problem: " + row["row_id"])
        if row["clay_navier_stokes_promoted"] or row["promotion_allowed"]:
            raise ValueError("row incorrectly allows promotion: " + row["row_id"])


def render_markdown(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 140 Constant Compatibility Ledger",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Sprint: `{summary['sprint']}` after Sprint `{summary['after_sprint']}`",
        f"- Parent route: `{summary['parent_route']}`",
        f"- Decision: `{summary['route_decision']}`",
        f"- Fail-closed: `{str(summary['fail_closed']).lower()}`",
        f"- Assembly remains conditional: `{str(summary['assembly_remains_conditional']).lower()}`",
        f"- Constant compatibility closed: `{str(summary['constant_compatibility_closed']).lower()}`",
        f"- Global barrier closed: `{str(summary['global_barrier_closed']).lower()}`",
        f"- Full Clay NS solved: `{str(summary['full_clay_ns_solved']).lower()}`",
        f"- Clay Navier-Stokes promoted: `{str(summary['clay_navier_stokes_promoted']).lower()}`",
        f"- Rows hash: `{summary['rows_hash']}`",
        "",
        "## Compatibility Rows",
        "",
        "| Row | Role | Status | Constants Available | Compatibility Closed | Absent Inputs | Row Hash |",
        "| --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in rows:
        absent = "; ".join(row["absent_inputs"])
        lines.append(
            "| "
            + f"`{row['row_id']}` | `{row['compatibility_role']}` | `{row['input_status']}` | "
            + f"`{str(row['constants_available']).lower()}` | "
            + f"`{str(row['compatibility_closed']).lower()}` | "
            + f"{absent} | `{row['row_hash']}` |"
        )
    lines.extend(
        [
            "",
            "## Why Conditional",
            "",
            (
                "The ledger requires all margins, radii, windows, log-loss, "
                "diffusion, and strain budgets to hold on a single crossing "
                "set.  Each analytic row records absent compatibility inputs, "
                "so the assembly can only be a conditional interface and not a "
                "closed regularity proof."
            ),
            "",
            "## Source Summary Hashes",
            "",
        ]
    )
    for key, digest in summary["source_summary_hashes"].items():
        lines.append(f"- {key}: `{digest}`")
    lines.extend(["", "## Control Card", ""])
    for key in ("O", "R", "C", "S", "L", "P", "G", "F"):
        lines.append(f"- {key}: {summary['control_card'][key]}")
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = repo_root / out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    rows = build_rows()
    summary = build_summary(repo_root, rows)
    validate(summary, rows)

    write_json(out_dir / SUMMARY_NAME, summary)
    write_json(out_dir / ROWS_JSON_NAME, rows)
    write_csv(out_dir / ROWS_CSV_NAME, rows)
    (out_dir / REPORT_NAME).write_text(render_markdown(summary, rows), encoding="utf-8")

    print(json.dumps(summary, indent=2, sort_keys=True))
    return int(summary["exit_code"])


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:  # pragma: no cover - CLI guard
        print(f"{CONTRACT}: validation failed: {exc}", file=sys.stderr)
        raise SystemExit(1)
