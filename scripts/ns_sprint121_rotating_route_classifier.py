#!/usr/bin/env python3
"""Sprint 121 NS rotating-route classifier."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint121_rotating_route_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint121_rotating_route_classifier")
SUMMARY_NAME = "ns_sprint121_rotating_route_classifier_summary.json"
ROWS_NAME = "ns_sprint121_rotating_route_classifier_rows.json"
REPORT_NAME = "ns_sprint121_rotating_route_classifier.md"

RECOMMENDED_NEXT_LEMMA = "NonCircularRotatingStrainPersistenceBound"
PRIMARY_ROUTE = "rotating_strain_phase_lag"


@dataclass(frozen=True)
class RotatingRoute:
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
        RotatingRoute(
            route_id="rotating_strain_phase_lag",
            classification="conditional_open_requires_persistence",
            recommendation_rank=1,
            complete=False,
            clay=False,
            next_action="prove " + RECOMMENDED_NEXT_LEMMA,
            rationale=(
                "The rotating strain phase-lag route remains conditionally open, "
                "but it needs a non-circular persistence bound before it can be "
                "promoted."
            ),
        ),
        RotatingRoute(
            route_id="constant_linear_strain",
            classification="obstructed_by_sprint120",
            recommendation_rank=5,
            complete=False,
            clay=False,
            next_action="retain as a Sprint120 obstruction record",
            rationale=(
                "Sprint120 blocks the constant linear strain lane, so it cannot "
                "serve as the Sprint121 rotating-route witness."
            ),
        ),
        RotatingRoute(
            route_id="nonlinear_feedback",
            classification="open_secondary",
            recommendation_rank=2,
            complete=False,
            clay=False,
            next_action="keep as a secondary mechanism after the persistence gate",
            rationale=(
                "Nonlinear feedback may support the construction later, but it "
                "does not replace the missing rotating-strain persistence bound."
            ),
        ),
        RotatingRoute(
            route_id="imposed_phase_lag",
            classification="rejected_circular",
            recommendation_rank=4,
            complete=False,
            clay=False,
            next_action="exclude from non-circular route accounting",
            rationale=(
                "An imposed phase lag assumes the phase separation the route must "
                "derive, making the argument circular."
            ),
        ),
        RotatingRoute(
            route_id="numerical_rotation_evidence",
            classification="empirical_not_proof",
            recommendation_rank=3,
            complete=False,
            clay=False,
            next_action="use only as empirical guidance, not as a lemma substitute",
            rationale=(
                "Numerical rotation evidence can guide tests, but it does not "
                "supply the analytic proof obligation."
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
        "open_route_count": sum(
            1
            for row in rows
            if row["classification"].startswith("open")
            or "open" in row["classification"]
        ),
        "obstructed_route_count": sum(
            1 for row in rows if row["classification"].startswith("obstructed")
        ),
        "rejected_route_count": sum(
            1 for row in rows if row["classification"].startswith("rejected")
        ),
        "empirical_route_count": sum(
            1 for row in rows if row["classification"].startswith("empirical")
        ),
        "exit_code": 1,
        "exit_reason": "rotating route remains conditional and not Clay-complete",
    }


def write_report(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    text = "\n".join(
        (
            f"# {CONTRACT}",
            "",
            "Deterministic Sprint121 classifier for NS rotating-route status.",
            "",
            f"Recommended next lemma: {summary['recommended_next_lemma']}",
            f"Recommended route id: {summary['recommended_route_id']}",
            f"Recommended classification: {summary['recommended_classification']}",
            f"Primary route: {summary['primary_route']}",
            f"Complete: {str(summary['complete']).lower()}",
            f"Clay: {str(summary['clay']).lower()}",
            "",
            "Exit status: 1 because no complete Clay route exists.",
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
