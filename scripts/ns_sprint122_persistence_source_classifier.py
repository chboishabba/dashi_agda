#!/usr/bin/env python3
"""Sprint 122 NS persistence source classifier."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint122_persistence_source_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint122_persistence_source_classifier")
SUMMARY_NAME = "ns_sprint122_persistence_source_classifier_summary.json"
ROWS_NAME = "ns_sprint122_persistence_source_classifier_rows.json"
REPORT_NAME = "ns_sprint122_persistence_source_classifier.md"

RECOMMENDED_NEXT_LEMMA = "RotatingFramePhaseLockingEstimate"
PRIMARY_ROUTE = "rotating_frame_ode"


@dataclass(frozen=True)
class PersistenceRoute:
    route_id: str
    classification: str
    recommendation_rank: int
    complete: bool
    clay: bool
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
        PersistenceRoute(
            route_id="rotating_frame_ode",
            classification="conditional_model_not_bound",
            recommendation_rank=1,
            complete=False,
            clay=False,
            next_action="prove " + RECOMMENDED_NEXT_LEMMA,
            rationale=(
                "The rotating-frame ODE gives the leading Sprint122 route, but "
                "it remains a conditional model until an analytic phase-locking "
                "estimate binds it to the Navier-Stokes evolution."
            ),
        ),
        PersistenceRoute(
            route_id="imposed_phase_lag",
            classification="rejected_circular",
            recommendation_rank=5,
            complete=False,
            clay=False,
            next_action="exclude from route accounting",
            rationale=(
                "An imposed phase lag supplies the relation the route is meant "
                "to derive, so it cannot close the persistence source."
            ),
        ),
        PersistenceRoute(
            route_id="numerical_phase_locking",
            classification="empirical_not_proof",
            recommendation_rank=4,
            complete=False,
            clay=False,
            next_action="use only as empirical guidance",
            rationale=(
                "Numerical phase locking can guide the target estimate, but it "
                "does not supply an analytic bound."
            ),
        ),
        PersistenceRoute(
            route_id="nonlinear_feedback",
            classification="open_secondary",
            recommendation_rank=2,
            complete=False,
            clay=False,
            next_action="keep as a secondary route after the primary estimate",
            rationale=(
                "Nonlinear feedback may support persistence once the frame "
                "estimate is available, but it does not replace that estimate."
            ),
        ),
        PersistenceRoute(
            route_id="global_data_realization",
            classification="open_downstream",
            recommendation_rank=3,
            complete=False,
            clay=False,
            next_action="defer until the conditional route is bounded",
            rationale=(
                "Global data realization depends on a verified local source, so "
                "it is downstream of the rotating-frame phase-locking estimate."
            ),
        ),
    ]
    return [route.row() for route in routes]


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def markdown_table(rows: list[dict[str, Any]]) -> str:
    headers = ("route_id", "classification", "complete", "clay", "next_action")
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
                    str(row["complete"]).lower(),
                    str(row["clay"]).lower(),
                    row["next_action"],
                )
            )
            + " |"
        )
    return "\n".join(lines)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    recommended = min(rows, key=lambda row: row["recommendation_rank"])
    complete = any(row["complete"] for row in rows)
    clay = any(row["clay"] for row in rows)
    return {
        "contract": CONTRACT,
        "route_count": len(rows),
        "candidate_routes": [row["route_id"] for row in rows],
        "classifications": {row["route_id"]: row["classification"] for row in rows},
        "recommended_next_lemma": RECOMMENDED_NEXT_LEMMA,
        "recommended_route_id": recommended["route_id"],
        "recommended_classification": recommended["classification"],
        "primary_route": PRIMARY_ROUTE,
        "complete": complete,
        "clay": clay,
        "clay_promoted": False,
        "clay_navier_stokes_promoted": False,
        "open_route_count": sum(1 for row in rows if "open" in row["classification"]),
        "rejected_route_count": sum(
            1 for row in rows if row["classification"].startswith("rejected")
        ),
        "empirical_route_count": sum(
            1 for row in rows if row["classification"].startswith("empirical")
        ),
        "conditional_route_count": sum(
            1 for row in rows if row["classification"].startswith("conditional")
        ),
        "exit_code": 1,
        "exit_reason": "no Clay route closes",
    }


def write_report(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    text = "\n".join(
        (
            f"# {CONTRACT}",
            "",
            "Deterministic Sprint122 classifier for NS persistence-source route status.",
            "",
            f"Recommended next lemma: {summary['recommended_next_lemma']}",
            f"Recommended route id: {summary['recommended_route_id']}",
            f"Recommended classification: {summary['recommended_classification']}",
            f"Primary route: {summary['primary_route']}",
            f"Complete: {str(summary['complete']).lower()}",
            f"Clay: {str(summary['clay']).lower()}",
            "",
            "Exit status: 1 because no Clay route closes.",
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
