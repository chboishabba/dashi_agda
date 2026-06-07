#!/usr/bin/env python3
"""Sprint 124 NS route classifier."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint124_route_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint124_route_classifier")
SUMMARY_NAME = "ns_sprint124_route_classifier_summary.json"
ROWS_NAME = "ns_sprint124_route_classifier_rows.json"
REPORT_NAME = "ns_sprint124_route_classifier.md"

RECOMMENDED_NEXT_LEMMA = "VortexStretchingAmplificationVsDepletionBound"
PRIMARY_ROUTE = "vortex_stretching"


@dataclass(frozen=True)
class Sprint124Route:
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
        Sprint124Route(
            route_id="favorable_phase_lag_window_lower_bound",
            classification="closed",
            recommendation_rank=4,
            complete=True,
            clay=False,
            next_action="retain as a closed Sprint123 input",
            rationale=(
                "The favorable phase-lag window lower bound is treated as closed "
                "for Sprint124 routing, but it does not by itself complete the "
                "Navier-Stokes Clay route."
            ),
        ),
        Sprint124Route(
            route_id="zero_mean_flux_over_rotation_cycle",
            classification="closed_obstruction",
            recommendation_rank=5,
            complete=False,
            clay=False,
            next_action="record as the controlling rotation-cycle obstruction",
            rationale=(
                "Zero mean flux over a rotation cycle closes the averaged-flux "
                "lane as an obstruction rather than as a positive route."
            ),
        ),
        Sprint124Route(
            route_id="rotating_strain_flux_budget",
            classification="obstructed_by_zero_mean",
            recommendation_rank=3,
            complete=False,
            clay=False,
            next_action="do not promote without defeating the zero-mean obstruction",
            rationale=(
                "The rotating strain flux budget remains blocked because the "
                "cycle-averaged contribution has zero mean."
            ),
        ),
        Sprint124Route(
            route_id="vortex_stretching",
            classification="live_primary_next",
            recommendation_rank=1,
            complete=False,
            clay=False,
            next_action="prove " + RECOMMENDED_NEXT_LEMMA,
            rationale=(
                "Vortex stretching is the live primary next route because it can "
                "target a nonzero amplification-versus-depletion imbalance after "
                "the rotating-flux obstruction."
            ),
        ),
        Sprint124Route(
            route_id="non_resonant_triads",
            classification="partial_open",
            recommendation_rank=2,
            complete=False,
            clay=False,
            next_action="keep as a secondary partial route after vortex stretching",
            rationale=(
                "Non-resonant triads remain partially open, but they do not yet "
                "supply the primary amplification bound needed for promotion."
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
    complete = all(row["complete"] for row in rows)
    clay = any(row["clay"] for row in rows)
    classifications = {row["route_id"]: row["classification"] for row in rows}
    return {
        "contract": CONTRACT,
        "route_count": len(rows),
        "candidate_routes": [row["route_id"] for row in rows],
        "classifications": classifications,
        "required_classifications_met": classifications
        == {
            "favorable_phase_lag_window_lower_bound": "closed",
            "zero_mean_flux_over_rotation_cycle": "closed_obstruction",
            "rotating_strain_flux_budget": "obstructed_by_zero_mean",
            "vortex_stretching": "live_primary_next",
            "non_resonant_triads": "partial_open",
        },
        "recommended_next_lemma": RECOMMENDED_NEXT_LEMMA,
        "recommended_route_id": recommended["route_id"],
        "recommended_classification": recommended["classification"],
        "primary_route": PRIMARY_ROUTE,
        "complete": complete,
        "clay": clay,
        "clay_promoted": False,
        "clay_navier_stokes_promoted": False,
        "closed_route_count": sum(
            1
            for row in rows
            if row["classification"].startswith("closed")
            or row["classification"].endswith("closed")
        ),
        "obstructed_route_count": sum(
            1 for row in rows if "obstruct" in row["classification"]
        ),
        "open_route_count": sum(1 for row in rows if "open" in row["classification"]),
        "live_route_count": sum(
            1 for row in rows if row["classification"].startswith("live")
        ),
        "exit_code": 1,
        "exit_reason": "NS Clay is not complete; vortex-stretching bound remains open",
    }


def write_report(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    text = "\n".join(
        (
            f"# {CONTRACT}",
            "",
            "Deterministic Sprint124 classifier for NS route status after the rotating-flux obstruction.",
            "",
            f"Recommended next lemma: {summary['recommended_next_lemma']}",
            f"Recommended route id: {summary['recommended_route_id']}",
            f"Recommended classification: {summary['recommended_classification']}",
            f"Primary route: {summary['primary_route']}",
            f"Required classifications met: {str(summary['required_classifications_met']).lower()}",
            f"Complete: {str(summary['complete']).lower()}",
            f"Clay: {str(summary['clay']).lower()}",
            "",
            "Exit status: 1 because NS Clay is not complete.",
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
