#!/usr/bin/env python3
"""Sprint 120 NS post-anti-correlation escape hatch classifier."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint120_escape_hatch_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint120_escape_hatch_classifier")
SUMMARY_NAME = "ns_sprint120_escape_hatch_classifier_summary.json"
ROWS_NAME = "ns_sprint120_escape_hatch_classifier_rows.json"
REPORT_NAME = "ns_sprint120_escape_hatch_classifier.md"

RECOMMENDED_NEXT_LEMMA = "RotatingStrainDecorrelationMechanism"
PRIMARY_OPEN_ROUTE = "rotating_strain"


@dataclass(frozen=True)
class EscapeHatchRoute:
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
        EscapeHatchRoute(
            route_id="constant_linear_strain_route",
            classification="obstructed_closed",
            recommendation_rank=5,
            complete=False,
            clay=False,
            next_action="retain only as a closed obstruction record",
            rationale=(
                "After the anti-correlation finding, constant linear strain cannot "
                "supply a non-circular positive route and is treated as closed."
            ),
        ),
        EscapeHatchRoute(
            route_id="rotating_strain",
            classification="remaining_open_requires_new_mechanism",
            recommendation_rank=1,
            complete=False,
            clay=False,
            next_action="prove " + RECOMMENDED_NEXT_LEMMA,
            rationale=(
                "Rotating strain is the only primary remaining lane because it "
                "could decorrelate the obstructing sign, but it needs a new "
                "mechanism rather than reuse of the anti-correlated route."
            ),
        ),
        EscapeHatchRoute(
            route_id="nonlinear_feedback",
            classification="self_interacting_packet_open",
            recommendation_rank=2,
            complete=False,
            clay=False,
            next_action="analyze self-interacting packet closure without imposed flux",
            rationale=(
                "Nonlinear packet feedback remains open as an internal mechanism, "
                "but it has not been promoted to a closed Clay route."
            ),
        ),
        EscapeHatchRoute(
            route_id="vorticity_coupling",
            classification="open_secondary",
            recommendation_rank=3,
            complete=False,
            clay=False,
            next_action="keep as a secondary coupling route",
            rationale=(
                "Vorticity coupling may support a later construction, but it is "
                "secondary to the rotating-strain decorrelation gate."
            ),
        ),
        EscapeHatchRoute(
            route_id="imposed_positive_flux",
            classification="rejected_circular",
            recommendation_rank=4,
            complete=False,
            clay=False,
            next_action="exclude from post-anti-correlation route accounting",
            rationale=(
                "Imposing positive flux assumes the sign the escape hatch must "
                "derive, so it is circular."
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
        "primary_open_route": PRIMARY_OPEN_ROUTE,
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
        "rejected_route_count": sum(
            1 for row in rows if row["classification"].startswith("rejected")
        ),
        "closed_route_count": sum(
            1
            for row in rows
            if row["classification"].endswith("closed")
            or "closed" in row["classification"]
        ),
        "exit_code": 1,
        "exit_reason": "post-anti-correlation escape hatch remains incomplete",
    }


def write_report(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    text = "\n".join(
        (
            f"# {CONTRACT}",
            "",
            "Deterministic Sprint120 classifier for post-anti-correlation NS route status.",
            "",
            f"Recommended next lemma: {summary['recommended_next_lemma']}",
            f"Recommended route id: {summary['recommended_route_id']}",
            f"Recommended classification: {summary['recommended_classification']}",
            f"Primary open route: {summary['primary_open_route']}",
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
