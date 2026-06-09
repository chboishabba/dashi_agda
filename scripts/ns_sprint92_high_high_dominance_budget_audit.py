#!/usr/bin/env python3
"""Sprint 92 NS high-high dominance budget audit.

Fail-closed decision audit for whether any allowed, non-circular existing
source closes HighHighDominanceAtDangerShell or
DangerShellDissipationDominatesInflux with both a pointwise H1 tail and an
independent coefficient.
"""

from __future__ import annotations

import argparse
import csv
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint92_high_high_dominance_budget_audit"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint92_high_high_dominance_budget_audit")
SUMMARY_NAME = "ns_sprint92_high_high_dominance_budget_audit_summary.json"
ROWS_JSON_NAME = "ns_sprint92_high_high_dominance_budget_audit_rows.json"
SOURCE_TABLE = "ns_sprint92_high_high_dominance_budget_source_table.csv"
GATE_TABLE = "ns_sprint92_high_high_dominance_budget_gate_table.csv"
REPORT_NAME = "ns_sprint92_high_high_dominance_budget_audit.md"

FAIL_CLOSED = "fail-closed"
ROUTE_OPEN = "NS_SPRINT92_HIGH_HIGH_DOMINANCE_BUDGET_ROUTE_OPEN"

FORBIDDEN_DEPENDENCIES = [
    "target_absorption",
    "bkm",
    "serrin",
    "h1_continuation",
    "theta_preservation",
    "desired_conclusion",
    "epsilon_from_absorption",
]

SUMMARY_INPUTS = {
    "sprint87_high_high_factorization": Path(
        "outputs/ns_sprint87_danger_shell_factorization_audit/"
        "ns_sprint87_danger_shell_factorization_summary.json"
    ),
    "sprint91_localized_identity": Path(
        "outputs/ns_sprint91_localized_flux_identity_audit/"
        "ns_sprint91_localized_flux_identity_audit_summary.json"
    ),
    "sprint90_local_enstrophy": Path(
        "outputs/ns_sprint90_local_enstrophy_budget_audit/"
        "ns_sprint90_local_enstrophy_budget_audit_summary.json"
    ),
    "sprint91_coefficient_independence": Path(
        "outputs/ns_sprint91_coefficient_independence_audit/"
        "ns_sprint91_coefficient_independence_audit_summary.json"
    ),
    "sprint87_absorption_scaling": Path(
        "outputs/ns_sprint87_absorption_scaling_audit/"
        "ns_sprint87_absorption_scaling_summary.json"
    ),
}


@dataclass(frozen=True)
class CandidateSource:
    source_id: str
    candidate_source: str
    source_kind: str
    source_surface: str
    evidence_summary_key: str
    allowed_source: bool
    closes_high_high_dominance_at_danger_shell: bool
    closes_danger_shell_dissipation_dominates_influx: bool
    supplies_pointwise_h1_tail: bool
    supplies_independent_coefficient: bool
    target_absorption: bool
    bkm: bool
    serrin: bool
    h1_continuation: bool
    theta_preservation: bool
    desired_conclusion: bool
    epsilon_from_absorption: bool
    classification: str
    evidence_note: str
    next_required_input: str

    @property
    def forbidden_hits(self) -> list[str]:
        return [name for name in FORBIDDEN_DEPENDENCIES if bool(getattr(self, name))]

    @property
    def avoids_forbidden_dependencies(self) -> bool:
        return not self.forbidden_hits

    @property
    def closes_target_obligation(self) -> bool:
        return (
            self.closes_high_high_dominance_at_danger_shell
            or self.closes_danger_shell_dissipation_dominates_influx
        )

    @property
    def evidence_complete(self) -> bool:
        return (
            self.closes_target_obligation
            and self.supplies_pointwise_h1_tail
            and self.supplies_independent_coefficient
        )

    @property
    def accepted(self) -> bool:
        return self.allowed_source and self.avoids_forbidden_dependencies and self.evidence_complete


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    return parser.parse_args()


def read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    return json.loads(path.read_text(encoding="utf-8"))


def candidate_sources() -> list[CandidateSource]:
    return [
        CandidateSource(
            source_id="S1",
            candidate_source="Sprint87 high-high factorization",
            source_kind="high-high factorization bookkeeping",
            source_surface=(
                "scripts/ns_sprint87_danger_shell_factorization_audit.py; "
                "DASHI/Physics/Closure/NSSprint87DangerShellSupFactorizationReceipt.agda"
            ),
            evidence_summary_key="sprint87_high_high_factorization",
            allowed_source=True,
            closes_high_high_dominance_at_danger_shell=False,
            closes_danger_shell_dissipation_dominates_influx=False,
            supplies_pointwise_h1_tail=False,
            supplies_independent_coefficient=False,
            target_absorption=False,
            bkm=False,
            serrin=False,
            h1_continuation=False,
            theta_preservation=False,
            desired_conclusion=False,
            epsilon_from_absorption=False,
            classification="FACTORIZATION_ONLY_ABSORPTION_OPEN",
            evidence_note=(
                "Sprint87 closes factorization support but leaves danger-shell absorption "
                "and the required H1-tail smallness scalar input open."
            ),
            next_required_input="non-circular pointwise H1 tail and coefficient before absorption",
        ),
        CandidateSource(
            source_id="S2",
            candidate_source="Sprint91 localized identity",
            source_kind="localized flux identity bookkeeping",
            source_surface=(
                "scripts/ns_sprint91_localized_flux_identity_audit.py; "
                "DASHI/Physics/Closure/NSSprint91LocalizedFluxIdentityAndCoefficientBudget.agda"
            ),
            evidence_summary_key="sprint91_localized_identity",
            allowed_source=True,
            closes_high_high_dominance_at_danger_shell=False,
            closes_danger_shell_dissipation_dominates_influx=False,
            supplies_pointwise_h1_tail=False,
            supplies_independent_coefficient=False,
            target_absorption=False,
            bkm=False,
            serrin=False,
            h1_continuation=False,
            theta_preservation=False,
            desired_conclusion=False,
            epsilon_from_absorption=False,
            classification="IDENTITY_BOOKKEEPING_ONLY",
            evidence_note=(
                "Sprint91 imports/localizes identity bookkeeping while keeping "
                "dangerShellDissipationDominatesInfluxClosed, pointwise tail, and "
                "independent coefficient gates false."
            ),
            next_required_input="analytic domination estimate with pointwise tail and independent coefficient",
        ),
        CandidateSource(
            source_id="S3",
            candidate_source="Adjacent leakage",
            source_kind="adjacent shell leakage estimate",
            source_surface="DASHI/Physics/Closure/NSAdjacentShellLeakageBoundReceipt.agda",
            evidence_summary_key="sprint87_absorption_scaling",
            allowed_source=True,
            closes_high_high_dominance_at_danger_shell=False,
            closes_danger_shell_dissipation_dominates_influx=False,
            supplies_pointwise_h1_tail=False,
            supplies_independent_coefficient=False,
            target_absorption=True,
            bkm=False,
            serrin=False,
            h1_continuation=False,
            theta_preservation=False,
            desired_conclusion=False,
            epsilon_from_absorption=True,
            classification="LEAKAGE_DEPENDS_ON_ABSORPTION_BUDGET",
            evidence_note=(
                "Adjacent leakage is useful only after an epsilon absorption budget is "
                "fixed; it is not an independent source for that budget."
            ),
            next_required_input="leakage coefficient fixed independently of target absorption",
        ),
        CandidateSource(
            source_id="S4",
            candidate_source="Sprint90 local enstrophy",
            source_kind="local enstrophy reduction/effect route",
            source_surface=(
                "scripts/ns_sprint90_local_enstrophy_budget_audit.py; "
                "DASHI/Physics/Closure/NSSprint90LocalEnstrophyDangerShellReductionReceipt.agda"
            ),
            evidence_summary_key="sprint90_local_enstrophy",
            allowed_source=True,
            closes_high_high_dominance_at_danger_shell=False,
            closes_danger_shell_dissipation_dominates_influx=False,
            supplies_pointwise_h1_tail=False,
            supplies_independent_coefficient=False,
            target_absorption=False,
            bkm=False,
            serrin=False,
            h1_continuation=False,
            theta_preservation=False,
            desired_conclusion=False,
            epsilon_from_absorption=False,
            classification="LOCAL_ENSTROPHY_REDUCTION_ONLY",
            evidence_note=(
                "Local enstrophy is recorded as a reduction/effect route, but the "
                "dissipation-dominates-influx, pointwise-tail, and coefficient gates "
                "remain analytically open."
            ),
            next_required_input="close local dissipation dominance and pointwise extraction non-circularly",
        ),
        CandidateSource(
            source_id="S5",
            candidate_source="Effect of target absorption",
            source_kind="target conclusion/effect",
            source_surface=(
                "DASHI/Physics/Closure/NSDangerShellMaxPrincipleConditionalProofReceipt.agda; "
                "DASHI/Physics/Closure/NSSprint87DangerShellSupFactorizationReceipt.agda"
            ),
            evidence_summary_key="sprint87_high_high_factorization",
            allowed_source=False,
            closes_high_high_dominance_at_danger_shell=True,
            closes_danger_shell_dissipation_dominates_influx=True,
            supplies_pointwise_h1_tail=False,
            supplies_independent_coefficient=False,
            target_absorption=True,
            bkm=False,
            serrin=False,
            h1_continuation=False,
            theta_preservation=False,
            desired_conclusion=True,
            epsilon_from_absorption=True,
            classification="FORBIDDEN_TARGET_CONCLUSION_SELF_USE",
            evidence_note=(
                "The effect of target absorption may describe consequences after the "
                "gate closes, but cannot be used as the non-circular source closing it."
            ),
            next_required_input="pre-absorption proof of dominance and coefficient",
        ),
        CandidateSource(
            source_id="S6",
            candidate_source="Sprint91 coefficient independence audit",
            source_kind="coefficient independence classifier",
            source_surface=(
                "scripts/ns_sprint91_coefficient_independence_audit.py; "
                "outputs/ns_sprint91_coefficient_independence_audit/"
                "ns_sprint91_coefficient_independence_audit_summary.json"
            ),
            evidence_summary_key="sprint91_coefficient_independence",
            allowed_source=True,
            closes_high_high_dominance_at_danger_shell=False,
            closes_danger_shell_dissipation_dominates_influx=False,
            supplies_pointwise_h1_tail=False,
            supplies_independent_coefficient=False,
            target_absorption=False,
            bkm=False,
            serrin=False,
            h1_continuation=False,
            theta_preservation=False,
            desired_conclusion=False,
            epsilon_from_absorption=False,
            classification="CLASSIFIER_REJECTS_ALL_CURRENT_SOURCES",
            evidence_note=(
                "The coefficient audit finds no allowed non-forbidden source with both "
                "pointwise H1 tail and an independent coefficient."
            ),
            next_required_input="new allowed source satisfying the single-source evidence rule",
        ),
    ]


def evidence_summaries(repo_root: Path) -> dict[str, dict[str, Any]]:
    return {key: read_json(repo_root / rel) for key, rel in SUMMARY_INPUTS.items()}


def source_rows(repo_root: Path) -> list[dict[str, Any]]:
    summaries = evidence_summaries(repo_root)
    rows: list[dict[str, Any]] = []
    for source in candidate_sources():
        summary = summaries.get(source.evidence_summary_key, {})
        forbidden_hits = source.forbidden_hits
        row = asdict(source)
        row.update(
            {
                "summary_path": SUMMARY_INPUTS[source.evidence_summary_key].as_posix(),
                "summary_present": bool(summary),
                "summary_route_decision": summary.get("route_decision", "missing"),
                "summary_complete": summary.get("complete", "missing"),
                "summary_fail_closed": summary.get("fail_closed", "missing"),
                "forbidden_hits": "; ".join(forbidden_hits) if forbidden_hits else "none",
                "forbidden_hit_count": len(forbidden_hits),
                "avoids_forbidden_dependencies": source.avoids_forbidden_dependencies,
                "closes_target_obligation": source.closes_target_obligation,
                "requires_pointwise_h1_tail": True,
                "requires_independent_coefficient": True,
                "requires_single_allowed_source": True,
                "evidence_complete": source.evidence_complete,
                "accepted": source.accepted,
                "route_decision": ROUTE_OPEN if source.accepted else FAIL_CLOSED,
            }
        )
        rows.append(row)
    return rows


def gate_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    allowed_non_forbidden = [
        row for row in rows if row["allowed_source"] and row["avoids_forbidden_dependencies"]
    ]
    allowed_target_closure = [row for row in allowed_non_forbidden if row["closes_target_obligation"]]
    allowed_pointwise = [row for row in allowed_target_closure if row["supplies_pointwise_h1_tail"]]
    allowed_coefficient = [
        row for row in allowed_target_closure if row["supplies_independent_coefficient"]
    ]
    accepted = [row for row in rows if row["accepted"]]
    specs = [
        (
            "G1",
            "ExistingSummariesPresent",
            all(row["summary_present"] for row in rows),
            "all referenced sprint audit summaries are present",
        ),
        (
            "G2",
            "AllowedNonCircularSource",
            bool(allowed_non_forbidden),
            "enumerate at least one allowed source with no forbidden dependency",
        ),
        (
            "G3",
            "AllowedTargetDominanceClosure",
            bool(allowed_target_closure),
            "close HighHighDominanceAtDangerShell or DangerShellDissipationDominatesInflux",
        ),
        (
            "G4",
            "PointwiseH1TailForTargetClosure",
            bool(allowed_pointwise),
            "supply pointwise H1 tail for the target dominance source",
        ),
        (
            "G5",
            "IndependentCoefficientForTargetClosure",
            bool(allowed_coefficient),
            "supply coefficient independent of absorption and forbidden continuation inputs",
        ),
        (
            "G6",
            "SameSourceEvidenceRule",
            bool(accepted),
            "one allowed non-circular source must supply closure, pointwise H1 tail, and coefficient",
        ),
        (
            "G7",
            "ForbiddenDependencyRejection",
            not any(row["accepted"] and row["forbidden_hit_count"] for row in rows),
            "reject target absorption, BKM, Serrin, H1 continuation, theta preservation, desired conclusion, epsilon_from_absorption",
        ),
    ]
    return [
        {
            "gate_id": gate_id,
            "gate_name": gate_name,
            "passed": passed,
            "status": "PASS" if passed else "FAIL_CLOSED",
            "next_required_input": next_required_input,
        }
        for gate_id, gate_name, passed, next_required_input in specs
    ]


def summary_payload(rows: list[dict[str, Any]], gates: list[dict[str, Any]]) -> dict[str, Any]:
    accepted = [row for row in rows if row["accepted"]]
    return {
        "contract": CONTRACT,
        "complete": bool(accepted),
        "route_decision": ROUTE_OPEN if accepted else FAIL_CLOSED,
        "final_decision": "ACCEPTED" if accepted else "FAIL_CLOSED",
        "fail_closed": not accepted,
        "candidate_source_count": len(rows),
        "accepted_source_count": len(accepted),
        "accepted_sources": [row["candidate_source"] for row in accepted],
        "required_residual_gate": (
            "exactly PointwiseH1TailWithIndependentEpsilonCoefficient"
        ),
        "residual_gate_exactly_recorded": (
            "exactly PointwiseH1TailWithIndependentEpsilonCoefficient"
        ),
        "high_high_gate_closed": False,
        "dominance_gate_closed": False,
        "clay_navier_stokes_promoted": False,
        "clay_promotion": False,
        "target_obligations": [
            "HighHighDominanceAtDangerShell",
            "DangerShellDissipationDominatesInflux",
        ],
        "forbidden_dependencies": FORBIDDEN_DEPENDENCIES,
        "single_source_evidence_rule_required": True,
        "allowed_non_circular_sources_considered": [
            row["candidate_source"]
            for row in rows
            if row["allowed_source"] and row["avoids_forbidden_dependencies"]
        ],
        "rejected_for_forbidden_dependencies": [
            {
                "candidate_source": row["candidate_source"],
                "forbidden_hits": row["forbidden_hits"],
            }
            for row in rows
            if row["forbidden_hit_count"]
        ],
        "any_allowed_target_closure": any(
            row["allowed_source"]
            and row["avoids_forbidden_dependencies"]
            and row["closes_target_obligation"]
            for row in rows
        ),
        "any_allowed_pointwise_h1_tail_for_target": any(
            row["allowed_source"]
            and row["avoids_forbidden_dependencies"]
            and row["closes_target_obligation"]
            and row["supplies_pointwise_h1_tail"]
            for row in rows
        ),
        "any_allowed_independent_coefficient_for_target": any(
            row["allowed_source"]
            and row["avoids_forbidden_dependencies"]
            and row["closes_target_obligation"]
            and row["supplies_independent_coefficient"]
            for row in rows
        ),
        "all_gates_passed": all(gate["passed"] for gate in gates),
        "fail_closed_reason": (
            "No allowed non-circular source closes a target dominance obligation "
            "with both pointwise H1 tail and an independent coefficient."
            if not accepted
            else "none"
        ),
        "rows_json": ROWS_JSON_NAME,
        "source_table": SOURCE_TABLE,
        "gate_table": GATE_TABLE,
        "report": REPORT_NAME,
        "open_obligations": [
            "prove HighHighDominanceAtDangerShell or DangerShellDissipationDominatesInflux before using absorption",
            "supply a pointwise-in-time H1 tail not derived from BKM/Serrin/H1 continuation/theta preservation",
            "fix the epsilon coefficient independently of target absorption",
            "record all three facts on one allowed source surface",
        ],
    }


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def markdown(summary: dict[str, Any], rows: list[dict[str, Any]], gates: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 92 High-High Dominance Budget Audit",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Decision: `{summary['final_decision']}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Candidate sources: `{summary['candidate_source_count']}`",
        f"- Accepted sources: `{summary['accepted_source_count']}`",
        "",
        "## Rule",
        "",
        (
            "The route opens only if one allowed source avoids target absorption, BKM, "
            "Serrin, H1 continuation, theta preservation, desired conclusion, and "
            "epsilon-from-absorption dependencies while supplying target dominance, "
            "a pointwise H1 tail, and an independent coefficient."
        ),
        "",
        "## Sources",
        "",
        "| Source | Target closure | H1 tail | Independent coefficient | Forbidden hits | Classification | Decision |",
        "| --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in rows:
        lines.append(
            f"| {row['candidate_source']} | `{row['closes_target_obligation']}` | "
            f"`{row['supplies_pointwise_h1_tail']}` | "
            f"`{row['supplies_independent_coefficient']}` | `{row['forbidden_hits']}` | "
            f"`{row['classification']}` | `{row['route_decision']}` |"
        )
    lines.extend(["", "## Gates", ""])
    for gate in gates:
        lines.append(f"- {gate['gate_id']} {gate['gate_name']}: `{gate['status']}`")
    lines.extend(["", "## Open Obligations", ""])
    lines.extend(f"- {item}" for item in summary["open_obligations"])
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    args = parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    rows = source_rows(args.repo_root)
    gates = gate_rows(rows)
    summary = summary_payload(rows, gates)

    (args.out_dir / ROWS_JSON_NAME).write_text(
        json.dumps(rows, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    write_csv(args.out_dir / SOURCE_TABLE, rows)
    write_csv(args.out_dir / GATE_TABLE, gates)
    (args.out_dir / SUMMARY_NAME).write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    (args.out_dir / REPORT_NAME).write_text(
        markdown(summary, rows, gates), encoding="utf-8"
    )
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
