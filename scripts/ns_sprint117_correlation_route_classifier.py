#!/usr/bin/env python3
"""Sprint 117 NS correlation route classifier."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint117_correlation_route_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint117_correlation_route_classifier")
SUMMARY_NAME = "ns_sprint117_correlation_route_classifier_summary.json"
ROWS_NAME = "ns_sprint117_correlation_route_classifier_rows.json"
REPORT_NAME = "ns_sprint117_correlation_route_classifier.md"

NEXT_LEMMA = "NonCircularGeometricCorrelationSource"
NEXT_CALCULATION = "sign of Pi_HH_to_L for kinematically forced compressive alignment"


@dataclass(frozen=True)
class CorrelationRoute:
    route_id: str
    classification: str
    clay_complete: bool
    clay_promoted: bool
    next_action: str
    rationale: str

    def row(self) -> dict[str, Any]:
        return asdict(self)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def route_rows() -> list[dict[str, Any]]:
    routes = [
        CorrelationRoute(
            route_id="thin_core_crow_option_b",
            classification="obstructed_by_sprint116",
            clay_complete=False,
            clay_promoted=False,
            next_action="do not promote through the Sprint116 Crow lane",
            rationale=(
                "Sprint116 records the thin-core Crow Option B route as blocked "
                "before it supplies a Clay-level correlation source."
            ),
        ),
        CorrelationRoute(
            route_id="finite_energy_swirl_option_b",
            classification="obstructed_by_volume_suppression",
            clay_complete=False,
            clay_promoted=False,
            next_action="keep as an obstruction record",
            rationale=(
                "Finite-energy swirl localization suppresses the needed volume "
                "contribution before the high-to-low transfer sign is closed."
            ),
        ),
        CorrelationRoute(
            route_id="singular_swirl_option_b",
            classification="rejected_infinite_l2",
            clay_complete=False,
            clay_promoted=False,
            next_action="exclude from Leray admissible route accounting",
            rationale=(
                "The singular swirl source falls outside the finite L2 data class "
                "needed for a Clay Navier-Stokes route."
            ),
        ),
        CorrelationRoute(
            route_id="concentration_based_option_b",
            classification="closed",
            clay_complete=False,
            clay_promoted=False,
            next_action="treat as closed unless a non-circular source is derived",
            rationale=(
                "The concentration-only route does not independently derive the "
                "geometric correlation needed for promotion."
            ),
        ),
        CorrelationRoute(
            route_id="non_circular_geometric_correlation_source",
            classification="open_primary_gate",
            clay_complete=False,
            clay_promoted=False,
            next_action="prove " + NEXT_LEMMA,
            rationale=(
                "This is the primary remaining gate because it targets the missing "
                "non-circular mechanism rather than assuming concentration closure."
            ),
        ),
        CorrelationRoute(
            route_id="option_a_sign_regular_route",
            classification="open",
            clay_complete=False,
            clay_promoted=False,
            next_action="compute " + NEXT_CALCULATION,
            rationale=(
                "The regular Option A route remains viable only after the decisive "
                "high-high to low-mode sign calculation is fixed."
            ),
        ),
        CorrelationRoute(
            route_id="burgers_vortex_concentration",
            classification="open_secondary",
            clay_complete=False,
            clay_promoted=False,
            next_action="hold as a secondary comparison route",
            rationale=(
                "The Burgers vortex lane can test concentration heuristics but does "
                "not outrank the non-circular geometric gate."
            ),
        ),
    ]
    return [route.row() for route in routes]


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def markdown_table(rows: list[dict[str, Any]]) -> str:
    headers = ("route_id", "classification", "clay_complete", "next_action")
    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    for row in rows:
        lines.append(
            "| "
            + " | ".join(
                (
                    row["route_id"],
                    row["classification"],
                    str(row["clay_complete"]).lower(),
                    row["next_action"],
                )
            )
            + " |"
        )
    return "\n".join(lines)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    clay_complete = any(row["clay_complete"] for row in rows)
    return {
        "contract": CONTRACT,
        "route_count": len(rows),
        "candidate_routes": [row["route_id"] for row in rows],
        "classifications": {row["route_id"]: row["classification"] for row in rows},
        "recommended_next_lemma": NEXT_LEMMA,
        "recommended_next_calculation": NEXT_CALCULATION,
        "primary_open_route": "non_circular_geometric_correlation_source",
        "secondary_open_routes": [
            "option_a_sign_regular_route",
            "burgers_vortex_concentration",
        ],
        "complete": clay_complete,
        "clay": clay_complete,
        "clay_promoted": False,
        "clay_navier_stokes_promoted": False,
        "exit_code": 1,
        "exit_reason": "no Clay-complete route",
    }


def write_report(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    text = "\n".join(
        (
            f"# {CONTRACT}",
            "",
            "Deterministic Sprint117 classifier for Navier-Stokes correlation routes.",
            "",
            f"Recommended next lemma: {summary['recommended_next_lemma']}",
            f"Recommended next calculation: {summary['recommended_next_calculation']}",
            f"Primary open route: {summary['primary_open_route']}",
            f"Clay-complete route exists: {str(summary['complete']).lower()}",
            "",
            "Exit status: 1 because no Clay-complete route exists.",
            "",
            markdown_table(rows),
            "",
        )
    )
    path.write_text(text, encoding="utf-8")


def main() -> int:
    args = parse_args()
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = args.repo_root / out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    rows = route_rows()
    summary = build_summary(rows)

    write_json(out_dir / ROWS_NAME, rows)
    write_json(out_dir / SUMMARY_NAME, summary)
    write_report(out_dir / REPORT_NAME, summary, rows)

    return 1


if __name__ == "__main__":
    sys.exit(main())
