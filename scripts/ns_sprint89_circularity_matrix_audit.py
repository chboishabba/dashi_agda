#!/usr/bin/env python3
"""Sprint 89 NS circularity matrix audit for the pointwise H1 tail gate.

The route is deliberately fail-closed.  A candidate route is allowed only when
it avoids every forbidden dependency class and supplies both required positive
inputs: a pointwise H1 tail and an independent epsilon coefficient.
"""

from __future__ import annotations

import argparse
import csv
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint89_circularity_matrix_audit"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint89_circularity_matrix_audit")
SUMMARY_NAME = "ns_sprint89_circularity_matrix_audit_summary.json"
MATRIX_JSON_NAME = "ns_sprint89_circularity_matrix_rows.json"
MATRIX_CSV_NAME = "ns_sprint89_circularity_matrix.csv"
REPORT_NAME = "ns_sprint89_circularity_matrix_audit.md"

FAIL_CLOSED = "fail-closed"
ROUTE_OPEN = "NS_SPRINT89_POINTWISE_H1_TAIL_ROUTE_OPEN"

FORBIDDEN_DEPENDENCIES = [
    "h1_continuation",
    "serrin",
    "bkm",
    "target_absorption",
    "theta_preservation",
    "clay_regularities",
    "desired_conclusion",
]


@dataclass(frozen=True)
class CandidateRoute:
    route_id: str
    candidate_input: str
    source_kind: str
    source_surface: str
    supplies_pointwise_h1_tail: bool
    supplies_independent_epsilon_coefficient: bool
    h1_continuation: bool
    serrin: bool
    bkm: bool
    target_absorption: bool
    theta_preservation: bool
    clay_regularities: bool
    desired_conclusion: bool
    classification: str
    reason: str
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
    def allowed_route(self) -> bool:
        return (
            self.avoids_forbidden_dependencies
            and self.supplies_pointwise_h1_tail
            and self.supplies_independent_epsilon_coefficient
        )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    return parser.parse_args()


def candidate_routes() -> list[CandidateRoute]:
    return [
        CandidateRoute(
            route_id="R1",
            candidate_input="Leray energy",
            source_kind="global weak energy inequality",
            source_surface="Leray energy / NS carrier energy receipts",
            supplies_pointwise_h1_tail=False,
            supplies_independent_epsilon_coefficient=False,
            h1_continuation=False,
            serrin=False,
            bkm=False,
            target_absorption=False,
            theta_preservation=False,
            clay_regularities=False,
            desired_conclusion=False,
            classification="INSUFFICIENT_ENERGY_LEVEL_ONLY",
            reason=(
                "The Leray energy inequality gives L2-level control and integrated "
                "dissipation information, not a pointwise H1 tail at the danger shell."
            ),
            next_required_input=(
                "non-circular localization theorem upgrading admissible weak data "
                "to pointwise H1 tail smallness"
            ),
        ),
        CandidateRoute(
            route_id="R2",
            candidate_input="KStar admissibility",
            source_kind="scale admissibility",
            source_surface="NSSprint86KStarHHalfTailObstructionReceipt / KStar route",
            supplies_pointwise_h1_tail=False,
            supplies_independent_epsilon_coefficient=False,
            h1_continuation=False,
            serrin=False,
            bkm=False,
            target_absorption=False,
            theta_preservation=False,
            clay_regularities=False,
            desired_conclusion=False,
            classification="INSUFFICIENT_SCALE_SELECTION_ONLY",
            reason=(
                "Admissibility of K*(t) selects a scale but does not itself provide "
                "H1-tail smallness or an independent absorption margin."
            ),
            next_required_input="tail theorem at the selected K*(t) plus independent epsilon coefficient",
        ),
        CandidateRoute(
            route_id="R3",
            candidate_input="Time-integrated dissipation",
            source_kind="integrated dissipation estimate",
            source_surface="NS dissipation/cutoff receipts",
            supplies_pointwise_h1_tail=False,
            supplies_independent_epsilon_coefficient=False,
            h1_continuation=False,
            serrin=False,
            bkm=False,
            target_absorption=False,
            theta_preservation=False,
            clay_regularities=False,
            desired_conclusion=False,
            classification="INSUFFICIENT_TIME_INTEGRATED",
            reason=(
                "An integral-in-time budget does not certify pointwise H1 tail "
                "smallness at the selected danger time without an additional "
                "non-circular extraction mechanism."
            ),
            next_required_input="pointwise-in-time extraction with independent small coefficient",
        ),
        CandidateRoute(
            route_id="R4",
            candidate_input="Danger-shell local mechanism",
            source_kind="localized absorption mechanism",
            source_surface="NSSprint87DangerShellSupFactorizationReceipt",
            supplies_pointwise_h1_tail=False,
            supplies_independent_epsilon_coefficient=False,
            h1_continuation=False,
            serrin=False,
            bkm=False,
            target_absorption=True,
            theta_preservation=False,
            clay_regularities=False,
            desired_conclusion=True,
            classification="FORBIDDEN_TARGET_REUSE",
            reason=(
                "The local danger-shell mechanism names the desired absorption/tail "
                "target.  Using it as the source would reuse the target conclusion."
            ),
            next_required_input="external local estimate not derived from the absorption conclusion",
        ),
        CandidateRoute(
            route_id="R5",
            candidate_input="Critical coefficient smallness",
            source_kind="coefficient-side smallness gate",
            source_surface="ns_sprint87_absorption_scaling_audit / scalar condition",
            supplies_pointwise_h1_tail=False,
            supplies_independent_epsilon_coefficient=False,
            h1_continuation=False,
            serrin=False,
            bkm=False,
            target_absorption=True,
            theta_preservation=False,
            clay_regularities=False,
            desired_conclusion=False,
            classification="INSUFFICIENT_COEFFICIENT_ONLY",
            reason=(
                "Coefficient smallness is a necessary scalar margin, but it cannot "
                "stand in for the pointwise H1 tail and is circular if obtained "
                "from the target absorption inequality."
            ),
            next_required_input="independent epsilon coefficient paired with a separate pointwise H1 tail route",
        ),
    ]


def route_rows(repo_root: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for route in candidate_routes():
        row = asdict(route)
        forbidden_hits = route.forbidden_hits
        row.update(
            {
                "forbidden_hits": "; ".join(forbidden_hits) if forbidden_hits else "none",
                "forbidden_hit_count": len(forbidden_hits),
                "avoids_forbidden_dependencies": route.avoids_forbidden_dependencies,
                "requires_pointwise_h1_tail": True,
                "requires_independent_epsilon_coefficient": True,
                "allowed_route": route.allowed_route,
                "route_decision": ROUTE_OPEN if route.allowed_route else FAIL_CLOSED,
                "source_surface_present": surface_present(repo_root, route.source_surface),
            }
        )
        rows.append(row)
    return rows


def surface_present(repo_root: Path, surface: str) -> bool:
    """Best-effort presence check for concrete path-like surface tokens."""
    path_tokens = re.findall(r"[\w./-]+\.(?:agda|py|json|md)", surface)
    for token in path_tokens:
        if (repo_root / token).exists():
            return True
    return False


def summary_payload(rows: list[dict[str, Any]]) -> dict[str, Any]:
    allowed_routes = [row for row in rows if row["allowed_route"]]
    any_forbidden = any(row["forbidden_hit_count"] for row in rows)
    any_pointwise_tail = any(row["supplies_pointwise_h1_tail"] for row in rows)
    any_independent_epsilon = any(row["supplies_independent_epsilon_coefficient"] for row in rows)
    decision = ROUTE_OPEN if allowed_routes else FAIL_CLOSED
    return {
        "contract": CONTRACT,
        "complete": False,
        "route_decision": decision,
        "fail_closed": decision == FAIL_CLOSED,
        "candidate_count": len(rows),
        "allowed_route_count": len(allowed_routes),
        "allowed_routes": [row["candidate_input"] for row in allowed_routes],
        "forbidden_dependencies": FORBIDDEN_DEPENDENCIES,
        "any_forbidden_dependency_detected": any_forbidden,
        "requires_single_allowed_route_with_both_inputs": True,
        "any_candidate_supplies_pointwise_h1_tail": any_pointwise_tail,
        "any_candidate_supplies_independent_epsilon_coefficient": any_independent_epsilon,
        "positive_gate_rule": (
            "route opens only when a candidate avoids H1 continuation, Serrin, BKM, "
            "target absorption, theta preservation, Clay regularity, and desired "
            "conclusion dependencies while supplying both pointwise H1 tail and "
            "an independent epsilon coefficient"
        ),
        "matrix_json": MATRIX_JSON_NAME,
        "matrix_csv": MATRIX_CSV_NAME,
        "report": REPORT_NAME,
        "open_obligations": [
            "supply a pointwise H1 tail theorem independent of continuation/Serrin/BKM/theta/Clay regularity",
            "supply an epsilon absorption coefficient not derived from target absorption",
            "verify both inputs occur on the same allowed route before opening the NS pointwise H1 tail gate",
        ],
    }


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def markdown(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 89 Circularity Matrix Audit",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Allowed routes: `{summary['allowed_route_count']}`",
        f"- Candidate routes: `{summary['candidate_count']}`",
        "",
        "## Rule",
        "",
        summary["positive_gate_rule"],
        "",
        "## Matrix",
        "",
        (
            "| Route | Candidate input | H1 tail | Independent epsilon | "
            "Forbidden hits | Classification | Decision |"
        ),
        "| --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in rows:
        lines.append(
            f"| `{row['route_id']}` | {row['candidate_input']} | "
            f"`{row['supplies_pointwise_h1_tail']}` | "
            f"`{row['supplies_independent_epsilon_coefficient']}` | "
            f"`{row['forbidden_hits']}` | `{row['classification']}` | "
            f"`{row['route_decision']}` |"
        )
    lines.extend(["", "## Next Required Inputs", ""])
    lines.extend(f"- {item}" for item in summary["open_obligations"])
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    args = parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    rows = route_rows(args.repo_root)
    summary = summary_payload(rows)

    (args.out_dir / MATRIX_JSON_NAME).write_text(
        json.dumps(rows, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    write_csv(args.out_dir / MATRIX_CSV_NAME, rows)
    (args.out_dir / SUMMARY_NAME).write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    (args.out_dir / REPORT_NAME).write_text(markdown(summary, rows), encoding="utf-8")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
