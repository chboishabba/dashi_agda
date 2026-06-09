#!/usr/bin/env python3
"""Sprint 123 NS phase-locking source classifier."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint123_phase_locking_source_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint123_phase_locking_source_classifier")
SUMMARY_NAME = "ns_sprint123_phase_locking_source_classifier_summary.json"
ROWS_NAME = "ns_sprint123_phase_locking_source_classifier_rows.json"
REPORT_NAME = "ns_sprint123_phase_locking_source_classifier.md"

RECOMMENDED_NEXT_LEMMA = "FavorablePhaseLagWindowLowerBound"
PRIMARY_ROUTE = "nse_derived_rotating_frame_ode"


@dataclass(frozen=True)
class PhaseLockingRoute:
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
        PhaseLockingRoute(
            route_id="nse_derived_rotating_frame_ode",
            classification="live_primary_requires_estimate",
            recommendation_rank=1,
            complete=False,
            clay=False,
            next_action="prove " + RECOMMENDED_NEXT_LEMMA,
            rationale=(
                "The NSE-derived rotating-frame ODE is the leading phase-locking "
                "source, but it still needs a favorable phase-lag window lower "
                "bound before route promotion."
            ),
        ),
        PhaseLockingRoute(
            route_id="imposed_phase_locking",
            classification="rejected_circular",
            recommendation_rank=6,
            complete=False,
            clay=False,
            next_action="exclude from source accounting",
            rationale=(
                "Imposed phase locking assumes the phase relation that the route "
                "must derive, so it cannot serve as an independent source."
            ),
        ),
        PhaseLockingRoute(
            route_id="sampled_dwell_windows",
            classification="empirical_not_proof",
            recommendation_rank=4,
            complete=False,
            clay=False,
            next_action="use only as empirical guidance for the window estimate",
            rationale=(
                "Sampled dwell windows can identify a plausible target interval, "
                "but they do not replace an analytic lower bound."
            ),
        ),
        PhaseLockingRoute(
            route_id="damping_drift_balance",
            classification="conditional_bound_missing",
            recommendation_rank=2,
            complete=False,
            clay=False,
            next_action="derive the missing bound after the primary estimate",
            rationale=(
                "The damping-drift balance is structurally relevant, but it "
                "remains conditional until the required inequality is proved."
            ),
        ),
        PhaseLockingRoute(
            route_id="global_data_realization",
            classification="open_downstream",
            recommendation_rank=3,
            complete=False,
            clay=False,
            next_action="defer until the local phase-locking source is bounded",
            rationale=(
                "Global data realization depends on a validated local source, so "
                "it remains downstream of the phase-lag window bound."
            ),
        ),
        PhaseLockingRoute(
            route_id="kstar_budget_bridge",
            classification="open_downstream",
            recommendation_rank=5,
            complete=False,
            clay=False,
            next_action="defer until the phase-locking lower bound is available",
            rationale=(
                "The k-star budget bridge can only transfer a locked window after "
                "the favorable phase-lag lower bound has been established."
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
        "live_route_count": sum(
            1 for row in rows if row["classification"].startswith("live")
        ),
        "exit_code": 1,
        "exit_reason": "phase-locking source still requires an analytic estimate",
    }


def write_report(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    text = "\n".join(
        (
            f"# {CONTRACT}",
            "",
            "Deterministic Sprint123 classifier for NS phase-locking source status.",
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
