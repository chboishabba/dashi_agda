#!/usr/bin/env python3
"""Sprint 91 NS coefficient-independence audit.

This audit is deliberately fail-closed.  A source opens the gate only if one
allowed source supplies both a pointwise H1 tail and an epsilon coefficient
that is independent of the target absorption step, while avoiding forbidden
dependencies.
"""

from __future__ import annotations

import argparse
import csv
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint91_coefficient_independence_audit"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint91_coefficient_independence_audit")
SUMMARY_NAME = "ns_sprint91_coefficient_independence_audit_summary.json"
ROWS_JSON_NAME = "ns_sprint91_coefficient_independence_rows.json"
ROWS_CSV_NAME = "ns_sprint91_coefficient_independence_rows.csv"
GATE_CSV_NAME = "ns_sprint91_coefficient_independence_gate_table.csv"
REPORT_NAME = "ns_sprint91_coefficient_independence_audit.md"

FAIL_CLOSED = "fail-closed"
ROUTE_OPEN = "NS_SPRINT91_COEFFICIENT_INDEPENDENCE_ROUTE_OPEN"

FORBIDDEN_DEPENDENCIES = [
    "h1_continuation",
    "serrin",
    "bkm",
    "target_absorption",
    "theta_preservation",
    "clay_regularities",
    "desired_conclusion",
    "epsilon_from_absorption",
]


@dataclass(frozen=True)
class CandidateSource:
    source_id: str
    candidate_source: str
    source_kind: str
    source_surface: str
    allowed_source: bool
    supplies_pointwise_h1_tail: bool
    supplies_independent_coefficient: bool
    h1_continuation: bool
    serrin: bool
    bkm: bool
    target_absorption: bool
    theta_preservation: bool
    clay_regularities: bool
    desired_conclusion: bool
    epsilon_from_absorption: bool
    classification: str
    evidence_note: str
    next_required_input: str

    @property
    def forbidden_hits(self) -> list[str]:
        return [
            dependency
            for dependency in FORBIDDEN_DEPENDENCIES
            if bool(getattr(self, dependency))
        ]

    @property
    def avoids_forbidden_dependencies(self) -> bool:
        return not self.forbidden_hits

    @property
    def evidence_complete(self) -> bool:
        return self.supplies_pointwise_h1_tail and self.supplies_independent_coefficient

    @property
    def accepted(self) -> bool:
        return self.allowed_source and self.avoids_forbidden_dependencies and self.evidence_complete


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    return parser.parse_args()


def candidate_sources() -> list[CandidateSource]:
    return [
        CandidateSource(
            source_id="S1",
            candidate_source="fixed-K LP identity",
            source_kind="fixed cutoff tail-flux identity",
            source_surface=(
                "DASHI/Physics/Closure/NSTailFluxLPIdentityAnalyticReceipt.agda; "
                "DASHI/Physics/Closure/NSTailFluxIdentityAnalyticTargetReceipt.agda"
            ),
            allowed_source=True,
            supplies_pointwise_h1_tail=False,
            supplies_independent_coefficient=False,
            h1_continuation=False,
            serrin=False,
            bkm=False,
            target_absorption=False,
            theta_preservation=False,
            clay_regularities=False,
            desired_conclusion=False,
            epsilon_from_absorption=False,
            classification="IDENTITY_ONLY_NO_POINTWISE_OR_COEFFICIENT",
            evidence_note=(
                "Records fixed-K flux bookkeeping and analytic target semantics, "
                "but not a pointwise H1 tail or independent epsilon coefficient."
            ),
            next_required_input=(
                "derive a non-circular pointwise H1 tail and a coefficient budget "
                "not chosen from the absorption conclusion"
            ),
        ),
        CandidateSource(
            source_id="S2",
            candidate_source="adjacent leakage bound",
            source_kind="adjacent shell influx estimate",
            source_surface="DASHI/Physics/Closure/NSAdjacentShellLeakageBoundReceipt.agda",
            allowed_source=True,
            supplies_pointwise_h1_tail=False,
            supplies_independent_coefficient=False,
            h1_continuation=False,
            serrin=False,
            bkm=False,
            target_absorption=True,
            theta_preservation=False,
            clay_regularities=False,
            desired_conclusion=False,
            epsilon_from_absorption=True,
            classification="TARGET_ABSORPTION_COEFFICIENT_REUSE",
            evidence_note=(
                "The leakage estimate is phrased against an epsilon absorption "
                "budget, so it cannot certify coefficient independence."
            ),
            next_required_input="external leakage coefficient fixed before invoking target absorption",
        ),
        CandidateSource(
            source_id="S3",
            candidate_source="local-enstrophy candidate",
            source_kind="danger-shell local enstrophy route",
            source_surface=(
                "DASHI/Physics/Closure/NSSprint90LocalEnstrophyDangerShellReductionReceipt.agda; "
                "scripts/ns_sprint90_local_enstrophy_budget_audit.py"
            ),
            allowed_source=True,
            supplies_pointwise_h1_tail=False,
            supplies_independent_coefficient=False,
            h1_continuation=False,
            serrin=False,
            bkm=False,
            target_absorption=False,
            theta_preservation=False,
            clay_regularities=False,
            desired_conclusion=False,
            epsilon_from_absorption=False,
            classification="REDUCTION_BOOKKEEPING_ONLY",
            evidence_note=(
                "Sprint 90 records local-enstrophy reduction bookkeeping while "
                "leaving actualPointwiseH1TailClosureClosed=false and "
                "independentEpsilonCoefficientClosed=false."
            ),
            next_required_input="close the local flux identity, pointwise extraction, and independent coefficient gates",
        ),
        CandidateSource(
            source_id="S4",
            candidate_source="scalar epsilon solver",
            source_kind="numeric/asymptotic scalar budget",
            source_surface="scripts/ns_sprint90_epsilon_budget_solver.py",
            allowed_source=True,
            supplies_pointwise_h1_tail=False,
            supplies_independent_coefficient=False,
            h1_continuation=False,
            serrin=False,
            bkm=False,
            target_absorption=False,
            theta_preservation=False,
            clay_regularities=False,
            desired_conclusion=False,
            epsilon_from_absorption=False,
            classification="SOLVER_REQUIRES_EVIDENCE",
            evidence_note=(
                "The scalar solver can check C*(K*)^-1/2*H1Tail <= epsilon*nu "
                "only after a supplied candidate already provides both required inputs."
            ),
            next_required_input="feed the solver an allowed supplied pointwise tail law with independent coefficient",
        ),
        CandidateSource(
            source_id="S5",
            candidate_source="target absorption",
            source_kind="desired absorption conclusion",
            source_surface="DASHI/Physics/Closure/NSAdjacentShellLeakageBoundReceipt.agda",
            allowed_source=False,
            supplies_pointwise_h1_tail=False,
            supplies_independent_coefficient=False,
            h1_continuation=False,
            serrin=False,
            bkm=False,
            target_absorption=True,
            theta_preservation=False,
            clay_regularities=False,
            desired_conclusion=True,
            epsilon_from_absorption=True,
            classification="FORBIDDEN_TARGET_SELF_USE",
            evidence_note=(
                "Using the target absorption inequality to choose the epsilon "
                "coefficient is circular and forbidden."
            ),
            next_required_input="coefficient source fixed independently before the absorption step",
        ),
    ]


def surface_present(repo_root: Path, surface: str) -> bool:
    path_tokens = re.findall(r"[\w./-]+\.(?:agda|py|json|md|csv)", surface)
    return any((repo_root / token).exists() for token in path_tokens)


def source_rows(repo_root: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for source in candidate_sources():
        row = asdict(source)
        forbidden_hits = source.forbidden_hits
        row.update(
            {
                "forbidden_hits": "; ".join(forbidden_hits) if forbidden_hits else "none",
                "forbidden_hit_count": len(forbidden_hits),
                "avoids_forbidden_dependencies": source.avoids_forbidden_dependencies,
                "requires_pointwise_h1_tail": True,
                "requires_independent_coefficient": True,
                "evidence_complete": source.evidence_complete,
                "accepted": source.accepted,
                "route_decision": ROUTE_OPEN if source.accepted else FAIL_CLOSED,
                "source_surface_present": surface_present(repo_root, source.source_surface),
            }
        )
        rows.append(row)
    return rows


def gate_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    any_allowed = any(row["allowed_source"] for row in rows)
    any_allowed_pointwise = any(
        row["allowed_source"] and row["avoids_forbidden_dependencies"] and row["supplies_pointwise_h1_tail"]
        for row in rows
    )
    any_allowed_independent = any(
        row["allowed_source"] and row["avoids_forbidden_dependencies"] and row["supplies_independent_coefficient"]
        for row in rows
    )
    any_single_complete = any(row["accepted"] for row in rows)
    return [
        {
            "gate_id": "G1",
            "gate_name": "AllowedSourceConsidered",
            "passed": any_allowed,
            "status": "PASS" if any_allowed else "FAIL_CLOSED",
            "next_required_input": "enumerate at least one allowed source surface",
        },
        {
            "gate_id": "G2",
            "gate_name": "AllowedPointwiseH1Tail",
            "passed": any_allowed_pointwise,
            "status": "PASS" if any_allowed_pointwise else "FAIL_CLOSED",
            "next_required_input": "supply pointwise H1 tail from an allowed non-forbidden source",
        },
        {
            "gate_id": "G3",
            "gate_name": "AllowedIndependentCoefficient",
            "passed": any_allowed_independent,
            "status": "PASS" if any_allowed_independent else "FAIL_CLOSED",
            "next_required_input": "supply epsilon coefficient independent of target absorption",
        },
        {
            "gate_id": "G4",
            "gate_name": "SameSourceEvidenceComplete",
            "passed": any_single_complete,
            "status": "PASS" if any_single_complete else "FAIL_CLOSED",
            "next_required_input": "provide both required inputs in one allowed source",
        },
    ]


def summary_payload(rows: list[dict[str, Any]], gates: list[dict[str, Any]]) -> dict[str, Any]:
    accepted = [row for row in rows if row["accepted"]]
    decision = ROUTE_OPEN if accepted else FAIL_CLOSED
    return {
        "contract": CONTRACT,
        "complete": bool(accepted),
        "route_decision": decision,
        "final_decision": "ACCEPTED" if accepted else "FAIL_CLOSED",
        "fail_closed": not accepted,
        "candidate_source_count": len(rows),
        "accepted_source_count": len(accepted),
        "accepted_sources": [row["candidate_source"] for row in accepted],
        "required_residual_gate": "PointwiseH1TailWithIndependentEpsilonCoefficient",
        "forbidden_dependencies": FORBIDDEN_DEPENDENCIES,
        "allowed_source_with_both_inputs": bool(accepted),
        "single_source_evidence_rule_required": True,
        "any_source_supplies_pointwise_h1_tail": any(row["supplies_pointwise_h1_tail"] for row in rows),
        "any_source_supplies_independent_coefficient": any(row["supplies_independent_coefficient"] for row in rows),
        "any_forbidden_dependency_detected": any(row["forbidden_hit_count"] for row in rows),
        "all_gates_passed": all(gate["passed"] for gate in gates),
        "positive_gate_rule": (
            "The route opens only if one allowed source avoids forbidden dependencies "
            "and supplies both pointwise H1 tail and an epsilon coefficient independent "
            "of target absorption."
        ),
        "fail_closed_reason": (
            "No allowed non-forbidden source supplies both pointwise H1 tail and an independent coefficient."
            if not accepted
            else "none"
        ),
        "rows_json": ROWS_JSON_NAME,
        "rows_csv": ROWS_CSV_NAME,
        "gate_csv": GATE_CSV_NAME,
        "report": REPORT_NAME,
        "open_obligations": [
            "prove a pointwise-in-time danger-shell H1 tail without continuation/Serrin/BKM/theta/Clay inputs",
            "fix an epsilon coefficient before and independently of target absorption",
            "record both facts on one allowed source surface before promoting the absorption route",
        ],
    }


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def markdown(summary: dict[str, Any], rows: list[dict[str, Any]], gates: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 91 Coefficient Independence Audit",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Decision: `{summary['final_decision']}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Candidate sources: `{summary['candidate_source_count']}`",
        f"- Accepted sources: `{summary['accepted_source_count']}`",
        "",
        "## Rule",
        "",
        summary["positive_gate_rule"],
        "",
        "## Candidate Sources",
        "",
        "| Source | H1 tail | Independent coefficient | Forbidden hits | Classification | Decision |",
        "| --- | --- | --- | --- | --- | --- |",
    ]
    for row in rows:
        lines.append(
            f"| {row['candidate_source']} | `{row['supplies_pointwise_h1_tail']}` | "
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
    write_csv(args.out_dir / ROWS_CSV_NAME, rows)
    write_csv(args.out_dir / GATE_CSV_NAME, gates)
    (args.out_dir / SUMMARY_NAME).write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    (args.out_dir / REPORT_NAME).write_text(
        markdown(summary, rows, gates), encoding="utf-8"
    )
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
