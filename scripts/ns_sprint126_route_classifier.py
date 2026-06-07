#!/usr/bin/env python3
"""Sprint 126 NS route-state classifier."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint126_route_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint126_route_classifier")
SUMMARY_NAME = "ns_sprint126_route_classifier_summary.json"
ROWS_NAME = "ns_sprint126_route_classifier_rows.json"
REPORT_NAME = "ns_sprint126_route_classifier.md"

RECOMMENDED_NEXT_LEMMA = "AxisymmetricBoundaryVortexStretchingGate"
PRIMARY_ROUTE = "axisymmetric_boundary_vortex_stretching_gate"

EXPECTED_CLASSIFICATIONS = {
    "sprint125_log_gap_unconditional": "corrected_open",
    "vortex_stretching_log_gap_conditional": "conditional_closed",
    "wavepacket_mode_coupling_no_go_tower": "partial_regularity_publishable",
    "axisymmetric_boundary_vortex_stretching_gate": "live_primary_next",
    "hou_luo_scaling_window": "compatible",
    "clay_navier_stokes": "not_promoted",
}


@dataclass(frozen=True)
class Sprint126Route:
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
        Sprint126Route(
            route_id="sprint125_log_gap_unconditional",
            classification="corrected_open",
            recommendation_rank=4,
            complete=False,
            clay=False,
            next_action="retain the corrected logarithmic gap as open",
            rationale=(
                "The Sprint125 unconditional logarithmic gap is corrected, but "
                "the correction does not close the Navier-Stokes route."
            ),
        ),
        Sprint126Route(
            route_id="vortex_stretching_log_gap_conditional",
            classification="conditional_closed",
            recommendation_rank=3,
            complete=True,
            clay=False,
            next_action="use only under its stated conditional hypotheses",
            rationale=(
                "The vortex-stretching logarithmic gap closes inside the "
                "conditional regime, without unconditional promotion."
            ),
        ),
        Sprint126Route(
            route_id="wavepacket_mode_coupling_no_go_tower",
            classification="partial_regularity_publishable",
            recommendation_rank=2,
            complete=False,
            clay=False,
            next_action="publish as partial regularity context",
            rationale=(
                "The wavepacket mode-coupling no-go tower is useful as a partial "
                "regularity result, not as a complete route."
            ),
        ),
        Sprint126Route(
            route_id="axisymmetric_boundary_vortex_stretching_gate",
            classification="live_primary_next",
            recommendation_rank=1,
            complete=False,
            clay=False,
            next_action="prove " + RECOMMENDED_NEXT_LEMMA,
            rationale=(
                "The axisymmetric boundary vortex-stretching gate is the live "
                "primary next route after the conditional log-gap closure."
            ),
        ),
        Sprint126Route(
            route_id="hou_luo_scaling_window",
            classification="compatible",
            recommendation_rank=5,
            complete=False,
            clay=False,
            next_action="keep as compatible scaling evidence",
            rationale=(
                "The Hou-Luo scaling window is compatible with the live gate, "
                "but does not independently promote the Clay claim."
            ),
        ),
        Sprint126Route(
            route_id="clay_navier_stokes",
            classification="not_promoted",
            recommendation_rank=6,
            complete=False,
            clay=False,
            next_action="do not promote until the live gate is closed",
            rationale=(
                "The Clay Navier-Stokes state remains not promoted because the "
                "axisymmetric boundary gate is still live."
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
    classifications = {row["route_id"]: row["classification"] for row in rows}
    return {
        "contract": CONTRACT,
        "route_count": len(rows),
        "candidate_routes": [row["route_id"] for row in rows],
        "classifications": classifications,
        "required_classifications_met": classifications == EXPECTED_CLASSIFICATIONS,
        "recommended_next_lemma": RECOMMENDED_NEXT_LEMMA,
        "recommended_route_id": recommended["route_id"],
        "recommended_classification": recommended["classification"],
        "primary_route": PRIMARY_ROUTE,
        "complete": False,
        "clay": False,
        "clay_promoted": False,
        "clay_navier_stokes_promoted": False,
        "closed_route_count": sum(
            1
            for row in rows
            if row["classification"].startswith("closed")
            or row["classification"].endswith("closed")
        ),
        "open_route_count": sum(1 for row in rows if "open" in row["classification"]),
        "live_route_count": sum(
            1 for row in rows if row["classification"].startswith("live")
        ),
        "compatible_route_count": sum(
            1 for row in rows if row["classification"] == "compatible"
        ),
        "exit_code": 1,
        "exit_reason": "NS is incomplete; axisymmetric boundary gate remains live",
    }


def write_report(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    text = "\n".join(
        (
            f"# {CONTRACT}",
            "",
            "Deterministic Sprint126 classifier for NS route state.",
            "",
            f"Recommended next lemma: {summary['recommended_next_lemma']}",
            f"Recommended route id: {summary['recommended_route_id']}",
            f"Recommended classification: {summary['recommended_classification']}",
            f"Primary route: {summary['primary_route']}",
            f"Required classifications met: {str(summary['required_classifications_met']).lower()}",
            f"Complete: {str(summary['complete']).lower()}",
            f"Clay: {str(summary['clay']).lower()}",
            "",
            "Exit status: 1 because NS is incomplete.",
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
