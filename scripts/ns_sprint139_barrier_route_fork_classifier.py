#!/usr/bin/env python3
"""Sprint 139 NS barrier route fork classifier.

This deterministic emitter ranks the post-Sprint 138 route forks for the
Hou-Luo-style axial monotonicity/barrier program.  It consumes no proof state
and proves no theorem; it records which routes remain open, which route is only
conditional, and when route-abandon/fallback should be selected.

The artifact is intentionally fail-closed.  Global proof remains open, the full
Clay Navier-Stokes problem is not solved, and no promotion is emitted.
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


CONTRACT = "ns_sprint139_barrier_route_fork_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint139_barrier_route_fork_classifier")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"

SPRINT = 139
AFTER_SPRINT = 138
PARENT_GATE = "AxialMonotonicityOfSwirlProfile"
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"

GLOBAL_CONCAVITY_ROUTE = "GlobalConcavityOfPsi1"
SECONDARY_PEAK_ROUTE = "SecondaryPeakExclusion"
TRANSPORT_COMMUTATOR_ROUTE = "TransportCommutatorDomination"
CONDITIONAL_REGULARITY_ROUTE = "ConditionalRegularityAssembly"
FALLBACK_ROUTE = "RouteAbandonFallback"

REQUIRED_ROUTE_IDS = {
    GLOBAL_CONCAVITY_ROUTE,
    SECONDARY_PEAK_ROUTE,
    TRANSPORT_COMMUTATOR_ROUTE,
    CONDITIONAL_REGULARITY_ROUTE,
    FALLBACK_ROUTE,
}

SOURCE_ARTIFACTS = {
    "global_concavity": "outputs/ns_sprint138_global_concavity_blocker/ns_sprint138_global_concavity_blocker_summary.json",
    "secondary_peak": "outputs/ns_sprint138_secondary_peak_exclusion/ns_sprint138_secondary_peak_exclusion_summary.json",
    "transport_commutator": "outputs/ns_sprint138_transport_commutator_budget/ns_sprint138_transport_commutator_budget_summary.json",
}

V_BARRIER_EQUATION = (
    "D_t v = nu Ltilde v + 2 v partial_z psi1 + 2 u1 partial_z^2 psi1 "
    "- (partial_z u^r) partial_r u1 - (partial_z u^z) v"
)

ROUTE_DECISION = "rank_routes_fail_closed"
PROMOTION_DECISION = "hold_no_clay_promotion"


@dataclass(frozen=True)
class RouteForkRow:
    route_id: str
    fork_label: str
    recommendation_rank: int
    classification: str
    sprint138_basis: tuple[str, ...]
    route_status: str
    closure_condition: str
    open_blockers: tuple[str, ...]
    evidence_for: tuple[str, ...]
    evidence_against: tuple[str, ...]
    route_action: str
    fallback_trigger: str
    conditional_regularness_needed: bool
    global_proof_open: bool
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool
    promotion_allowed: bool

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        for key in (
            "sprint138_basis",
            "open_blockers",
            "evidence_for",
            "evidence_against",
        ):
            row[key] = list(row[key])
        row["blocker_id"] = self.route_id
        row["blocker_status"] = self.route_status
        row["blocked_claim"] = self.closure_condition
        row["missing_input"] = list(self.open_blockers)
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
        RouteForkRow(
            route_id=GLOBAL_CONCAVITY_ROUTE,
            fork_label="Fork A",
            recommendation_rank=3,
            classification="open_primary_blocker",
            sprint138_basis=(
                "ns_sprint138_global_concavity_blocker",
                "local Taylor concavity supported only near the symmetry center",
            ),
            route_status="open_not_promotable",
            closure_condition=(
                "Prove a boundary-compatible nonlocal theorem forcing "
                "partial_z^2 psi1 to have the sign or domination margin needed "
                "at every possible first positive maximum of v."
            ),
            open_blockers=(
                "elliptic nonlocal psi1 dependence",
                "sign-indefinite differentiated kernel contribution",
                "boundary and annular source contribution",
                "time persistence of the concavity sign",
            ),
            evidence_for=(
                "local center expansion gives candidate favorable sign",
                "Sprint 138 isolates the exact missing theorem",
            ),
            evidence_against=(
                "nonlocal elliptic coupling can reverse the local sign ledger",
                "local support does not control off-center first crossings",
            ),
            route_action="keep_open_but_do_not_promote",
            fallback_trigger=(
                "Select fallback if global sign/dominance is refuted or cannot "
                "be made boundary- and annulus-compatible."
            ),
            conditional_regularness_needed=True,
            global_proof_open=True,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        RouteForkRow(
            route_id=SECONDARY_PEAK_ROUTE,
            fork_label="Fork B",
            recommendation_rank=4,
            classification="open_shape_persistence_blocker",
            sprint138_basis=(
                "ns_sprint138_secondary_peak_exclusion",
                "single-peak initial shape is recorded but not persistent",
            ),
            route_status="open_not_promotable",
            closure_condition=(
                "Prove no secondary axial peak, shoulder, or positive local "
                "maximum of v can form outside the primary barrier region "
                "during the relevant time window."
            ),
            open_blockers=(
                "nonlinear source can form shoulders",
                "annular Gamma/u1 constraints do not control v zero count",
                "coupled axisymmetric Sturmian zero-number principle absent",
                "secondary off-peak positive-v crossing remains possible",
            ),
            evidence_for=(
                "initial single-peak hypothesis can start a first-crossing argument",
                "viscous smoothing helps regularity of the profile",
            ),
            evidence_against=(
                "source terms are not scalar heat flow",
                "radial dependence and nonlocal feedback break 1D zero-count templates",
            ),
            route_action="keep_open_after_higher_priority_routes",
            fallback_trigger=(
                "Select fallback if a secondary crossing scenario survives all "
                "reasonable localization or zero-count replacements."
            ),
            conditional_regularness_needed=True,
            global_proof_open=True,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        RouteForkRow(
            route_id=TRANSPORT_COMMUTATOR_ROUTE,
            fork_label="Fork C",
            recommendation_rank=2,
            classification="open_budget_domination_route",
            sprint138_basis=(
                "ns_sprint138_transport_commutator_budget",
                V_BARRIER_EQUATION,
            ),
            route_status="open_high_priority",
            closure_condition=(
                "Prove pointwise sign or log-aware integrated domination for "
                "-(partial_z u^r) partial_r u1 at every possible first positive "
                "maximum of v."
            ),
            open_blockers=(
                "nonhomogeneous radial commutator injects source independent of v",
                "incompressibility does not fix sign correlation",
                "log Biot-Savart strain loss remains open",
                "global barrier closure unavailable",
            ),
            evidence_for=(
                "the commutator term is explicitly isolated",
                "possible pointwise or integrated domination hypotheses are concrete",
            ),
            evidence_against=(
                "the term can be positive at first crossing",
                "available divergence-free identities are constraint equations, not domination",
            ),
            route_action="prioritize_as_next_analytic_fork",
            fallback_trigger=(
                "Select fallback if log-aware commutator domination cannot be "
                "absorbed by any local concavity or weighted barrier margin."
            ),
            conditional_regularness_needed=True,
            global_proof_open=True,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        RouteForkRow(
            route_id=CONDITIONAL_REGULARITY_ROUTE,
            fork_label="Fork D",
            recommendation_rank=1,
            classification="conditional_assembly_not_global_proof",
            sprint138_basis=(
                "assemble GlobalConcavityOfPsi1",
                "assemble SecondaryPeakExclusion",
                "assemble TransportCommutatorDomination",
            ),
            route_status="conditional_best_next_artifact",
            closure_condition=(
                "Assemble a conditional theorem: if global concavity/dominance, "
                "secondary peak exclusion, and commutator domination all hold "
                "with compatible constants, then the local v barrier can feed a "
                "conditional regularity statement for the monitored route."
            ),
            open_blockers=(
                GLOBAL_CONCAVITY_ROUTE,
                SECONDARY_PEAK_ROUTE,
                TRANSPORT_COMMUTATOR_ROUTE,
                "constant compatibility across all three conditions",
                "translation from route regularity to full Clay class absent",
            ),
            evidence_for=(
                "Sprint 138 separated the three exact missing gates",
                "conditional assembly can check interface compatibility without claiming proof",
            ),
            evidence_against=(
                "all analytic gates remain open",
                "conditional route regularity is weaker than a full Clay Navier-Stokes solution",
            ),
            route_action="rank_first_for_next_deterministic_artifact",
            fallback_trigger=(
                "Do not use as fallback; use this only to make dependencies and "
                "constants explicit while keeping the theorem conditional."
            ),
            conditional_regularness_needed=True,
            global_proof_open=True,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        RouteForkRow(
            route_id=FALLBACK_ROUTE,
            fork_label="Fork E",
            recommendation_rank=5,
            classification="abandon_or_fallback_if_blockers_harden",
            sprint138_basis=(
                "global concavity open",
                "secondary peak exclusion open",
                "transport commutator domination open",
            ),
            route_status="fallback_available_not_selected_first",
            closure_condition=(
                "Abandon the barrier-promotion route or fall back to a weaker "
                "obstruction/result ledger if any required Sprint 138 blocker "
                "is refuted, incompatible, or cannot be localized."
            ),
            open_blockers=(
                "proof route may be overconstrained",
                "conditional assumptions may not be simultaneously satisfiable",
                "available evidence may support only obstruction classification",
            ),
            evidence_for=(
                "fail-closed route accounting avoids accidental Clay promotion",
                "fallback preserves useful obstruction information",
            ),
            evidence_against=(
                "fallback is not a regularity proof",
                "fallback abandons the direct barrier closure attempt",
            ),
            route_action="hold_as_route_abandon_decision_point",
            fallback_trigger=(
                "Trigger when one of the three analytic gates is proved false "
                "or becomes structurally incompatible with the others."
            ),
            conditional_regularness_needed=False,
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
    fieldnames = (
        "route_id",
        "fork_label",
        "recommendation_rank",
        "classification",
        "sprint138_basis",
        "route_status",
        "closure_condition",
        "open_blockers",
        "evidence_for",
        "evidence_against",
        "route_action",
        "fallback_trigger",
        "conditional_regularness_needed",
        "global_proof_open",
        "full_clay_ns_solved",
        "clay_navier_stokes_promoted",
        "promotion_allowed",
        "blocker_id",
        "blocker_status",
        "blocked_claim",
        "missing_input",
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
                "sprint138_basis",
                "open_blockers",
                "evidence_for",
                "evidence_against",
                "missing_input",
            ):
                serializable[key] = "; ".join(serializable[key])
            writer.writerow(serializable)


def build_summary(repo_root: Path, rows: list[dict[str, Any]]) -> dict[str, Any]:
    route_ids = {row["route_id"] for row in rows}
    missing_required = sorted(REQUIRED_ROUTE_IDS.difference(route_ids))
    ranked = sorted(rows, key=lambda row: row["recommendation_rank"])
    source_hashes = {
        key: file_sha256(repo_root / relative_path)
        for key, relative_path in SOURCE_ARTIFACTS.items()
    }
    row_hashes = {row["route_id"]: row["row_hash"] for row in rows}
    rows_hash = stable_hash(rows)

    invariant_failures: list[str] = []
    if missing_required:
        invariant_failures.append("missing_required_routes:" + ",".join(missing_required))
    if ranked[0]["route_id"] != CONDITIONAL_REGULARITY_ROUTE:
        invariant_failures.append("conditional_regularness_not_ranked_first")
    if ranked[1]["route_id"] != TRANSPORT_COMMUTATOR_ROUTE:
        invariant_failures.append("transport_commutator_not_ranked_second")
    if not all(row["global_proof_open"] for row in rows):
        invariant_failures.append("global_proof_not_open_in_all_rows")
    if any(row["full_clay_ns_solved"] for row in rows):
        invariant_failures.append("full_clay_ns_solved_detected")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        invariant_failures.append("clay_promotion_detected")
    if any(row["promotion_allowed"] for row in rows):
        invariant_failures.append("promotion_allowed_detected")
    if not any(row["route_id"] == FALLBACK_ROUTE for row in rows):
        invariant_failures.append("fallback_route_missing")
    if not any("conditional" in row["classification"] for row in rows):
        invariant_failures.append("conditional_assembly_missing")
    if not any("abandon" in row["classification"] for row in rows):
        invariant_failures.append("route_abandon_classification_missing")

    invariants_passed = not invariant_failures
    classifications = {row["route_id"]: row["classification"] for row in rows}

    return {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "after_sprint": AFTER_SPRINT,
        "program": PROGRAM,
        "parent_gate": PARENT_GATE,
        "row_count": len(rows),
        "route_count": len(rows),
        "candidate_routes": [row["route_id"] for row in ranked],
        "classifications": classifications,
        "ranked_route_ids": [row["route_id"] for row in ranked],
        "recommended_next_route": ranked[0]["route_id"],
        "recommended_next_action": ranked[0]["route_action"],
        "second_priority_route": ranked[1]["route_id"],
        "route_decision": ROUTE_DECISION,
        "decision": "fail_closed_ranked_forks",
        "promotion_decision": PROMOTION_DECISION,
        "global_proof_open": True,
        "global_proof_proved": False,
        "global_proof_proven": False,
        "global_barrier_closed": False,
        "axial_monotonicity_gate_closed": False,
        "conditional_regularness_assembly_ranked_first": True,
        "conditional_regularness_is_full_proof": False,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "clay_promoted": False,
        "promotion_allowed": False,
        "fallback_route_available": True,
        "fallback_route_id": FALLBACK_ROUTE,
        "open_routes": [
            row["route_id"]
            for row in rows
            if row["global_proof_open"] and not row["clay_navier_stokes_promoted"]
        ],
        "source_artifacts": SOURCE_ARTIFACTS,
        "source_summary_hashes": source_hashes,
        "row_hashes": row_hashes,
        "rows_hash": rows_hash,
        "summary_payload_hash_without_self": stable_hash(
            {
                "contract": CONTRACT,
                "ranked_route_ids": [row["route_id"] for row in ranked],
                "classifications": classifications,
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
                "Worker 2 owns only scripts/ns_sprint139_barrier_route_fork_classifier.py "
                "and outputs/ns_sprint139_barrier_route_fork_classifier/."
            ),
            "R": (
                "Rank/fork the post-Sprint 138 routes: GlobalConcavityOfPsi1, "
                "SecondaryPeakExclusion, TransportCommutatorDomination, "
                "conditional regularity assembly, and route-abandon/fallback."
            ),
            "C": (
                "Deterministic stdlib Python emitter with dataclass rows, "
                "stable SHA-256 hashes, validation, JSON, CSV, and Markdown."
            ),
            "S": (
                "Conditional assembly is ranked first as the next artifact, "
                "transport commutator domination second as the next analytic "
                "fork, all global proof and Clay promotion flags remain false."
            ),
            "L": (
                "Sprint 138 blockers -> ranked route forks -> conditional "
                "assembly surface -> fallback if blockers harden or conflict."
            ),
            "P": (
                "Use this classifier to guide Sprint 139 route selection while "
                "explicitly keeping the global proof open."
            ),
            "G": (
                "Validation passes only if every row keeps global_proof_open "
                "true and full Clay/Clay promotion/promotion_allowed false."
            ),
            "F": (
                "Missing route rows, accidental global closure, full Clay NS "
                "claim, Clay promotion, or missing fallback fails validation."
            ),
        },
    }


def validate(summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    route_ids = {row["route_id"] for row in rows}
    missing = REQUIRED_ROUTE_IDS.difference(route_ids)
    if missing:
        raise ValueError("missing required routes: " + ", ".join(sorted(missing)))
    if summary["contract"] != CONTRACT:
        raise ValueError("wrong contract")
    if summary["sprint"] != SPRINT or summary["after_sprint"] != AFTER_SPRINT:
        raise ValueError("wrong sprint metadata")
    if summary["route_decision"] != ROUTE_DECISION:
        raise ValueError("wrong route decision")
    if summary["recommended_next_route"] != CONDITIONAL_REGULARITY_ROUTE:
        raise ValueError("conditional regularity assembly must rank first")
    if summary["second_priority_route"] != TRANSPORT_COMMUTATOR_ROUTE:
        raise ValueError("transport commutator route must rank second")
    if not summary["global_proof_open"]:
        raise ValueError("global proof must remain open")
    if summary["global_proof_proved"] or summary["global_proof_proven"]:
        raise ValueError("global proof must not be proved")
    if summary["global_barrier_closed"] or summary["axial_monotonicity_gate_closed"]:
        raise ValueError("barrier/gate closure must not be claimed")
    if summary["conditional_regularness_is_full_proof"]:
        raise ValueError("conditional assembly must not be treated as full proof")
    if summary["full_clay_ns_solved"]:
        raise ValueError("full Clay NS must remain unsolved")
    if summary["clay_navier_stokes_promoted"] or summary["clay_promoted"]:
        raise ValueError("Clay promotion is forbidden")
    if summary["promotion_allowed"]:
        raise ValueError("promotion must not be allowed")
    if not summary["fallback_route_available"]:
        raise ValueError("fallback route must be available")
    if not all(row["global_proof_open"] for row in rows):
        raise ValueError("all rows must keep global proof open")
    if any(row["full_clay_ns_solved"] for row in rows):
        raise ValueError("row claims full Clay NS solved")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        raise ValueError("row promotes Clay Navier-Stokes")
    if any(row["promotion_allowed"] for row in rows):
        raise ValueError("row allows promotion")
    if len({row["row_hash"] for row in rows}) != len(rows):
        raise ValueError("row hashes must be unique")
    if summary["invariant_failures"]:
        raise ValueError("; ".join(summary["invariant_failures"]))


def build_report(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    ranked = sorted(rows, key=lambda row: row["recommendation_rank"])
    lines = [
        "# NS Sprint 139 Barrier Route Fork Classifier",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Sprint: `{summary['sprint']}` after Sprint `{summary['after_sprint']}`",
        f"- Parent gate: `{summary['parent_gate']}`",
        f"- Decision: `{summary['decision']}`",
        f"- Recommended next route: `{summary['recommended_next_route']}`",
        f"- Second priority route: `{summary['second_priority_route']}`",
        f"- Global proof open: `{str(summary['global_proof_open']).lower()}`",
        f"- Global barrier closed: `{str(summary['global_barrier_closed']).lower()}`",
        f"- Full Clay NS solved: `{str(summary['full_clay_ns_solved']).lower()}`",
        f"- Clay Navier-Stokes promoted: `{str(summary['clay_navier_stokes_promoted']).lower()}`",
        f"- Rows hash: `{summary['rows_hash']}`",
        "",
        "## Ranked Routes",
        "",
        "| Rank | Route | Classification | Status | Action | Fallback Trigger | Row Hash |",
        "| --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in ranked:
        trigger = row["fallback_trigger"].replace("|", "\\|")
        action = row["route_action"].replace("|", "\\|")
        lines.append(
            f"| {row['recommendation_rank']} | `{row['route_id']}` | "
            f"`{row['classification']}` | `{row['route_status']}` | "
            f"{action} | {trigger} | `{row['row_hash']}` |"
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
                "This artifact ranks route work only. It keeps the global proof "
                "open, treats conditional regularity assembly as conditional, "
                "and emits no full Clay Navier-Stokes solution or promotion."
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
                "contract": summary["contract"],
                "exit_code": summary["exit_code"],
                "full_clay_ns_solved": summary["full_clay_ns_solved"],
                "global_proof_open": summary["global_proof_open"],
                "recommended_next_route": summary["recommended_next_route"],
                "rows_hash": summary["rows_hash"],
            },
            sort_keys=True,
        )
    )
    return int(summary["exit_code"])


if __name__ == "__main__":
    sys.exit(main())
