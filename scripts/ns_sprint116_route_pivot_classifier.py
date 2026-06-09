#!/usr/bin/env python3
"""Sprint 116 post-Crow NS route pivot classifier."""

from __future__ import annotations

import argparse
import csv
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint116_route_pivot_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint116_route_pivot_classifier")
SUMMARY_NAME = "ns_sprint116_route_pivot_classifier_summary.json"
ROWS_NAME = "ns_sprint116_route_pivot_classifier_rows.json"
CSV_NAME = "ns_sprint116_route_pivot_classifier_rows.csv"
REPORT_NAME = "ns_sprint116_route_pivot_classifier.md"

RECOMMENDED_NEXT_ROUTE = "axisymmetric_with_swirl_option_a"
RECOMMENDED_NEXT_LEMMA = "SwirlingVelocityStrainSign"


@dataclass(frozen=True)
class RouteChoice:
    route_id: str
    status: str
    reuses_in_repo: str
    next_lemma: str
    clay_promoted: bool
    recommendation_rank: int
    complete: bool
    clay: bool
    rationale: str

    def row(self) -> dict[str, Any]:
        return asdict(self)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def route_choices() -> list[RouteChoice]:
    return [
        RouteChoice(
            route_id="thin_core_crow_option_b",
            status="obstructed",
            reuses_in_repo=(
                "Sprint113-115 Crow persistence, thin-core reconnection window, "
                "and flux-budget classifiers"
            ),
            next_lemma="NoUnforcedCrowFluxCollapse",
            clay_promoted=False,
            recommendation_rank=3,
            complete=False,
            clay=False,
            rationale=(
                "The post-Crow path is blocked by the missing unforced nonlinear "
                "reconnection-window lower bound and k-star collapse threshold."
            ),
        ),
        RouteChoice(
            route_id="axisymmetric_with_swirl_option_a",
            status="open_high_value",
            reuses_in_repo=(
                "axisymmetric Navier-Stokes structure, swirl sign bookkeeping, "
                "and strain/vorticity closure surfaces"
            ),
            next_lemma=RECOMMENDED_NEXT_LEMMA,
            clay_promoted=False,
            recommendation_rank=1,
            complete=False,
            clay=False,
            rationale=(
                "This route avoids the Crow reconnection obstruction and has a "
                "concrete next lemma with high leverage for post-pivot progress."
            ),
        ),
        RouteChoice(
            route_id="burgers_vortex_concentration_option_b",
            status="open_long_shot",
            reuses_in_repo=(
                "vortex concentration heuristics and local strain amplification "
                "interfaces"
            ),
            next_lemma="BurgersVortexConcentrationBarrier",
            clay_promoted=False,
            recommendation_rank=2,
            complete=False,
            clay=False,
            rationale=(
                "The route remains admissible but has a weaker direct bridge from "
                "model concentration to an unforced Clay-level Navier-Stokes claim."
            ),
        ),
        RouteChoice(
            route_id="general_data_kstar_regular_option_a",
            status="blocked_by_sprints87_94",
            reuses_in_repo=(
                "general-data k-star regularity attempts and Sprint87-94 blocker "
                "records"
            ),
            next_lemma="GeneralDataKStarRegularityBlockerDischarge",
            clay_promoted=False,
            recommendation_rank=4,
            complete=False,
            clay=False,
            rationale=(
                "The known Sprint87-94 blockers still prevent promotion of the "
                "general-data k-star regular route."
            ),
        ),
    ]


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        raise ValueError("cannot write empty route set")
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def markdown_table(rows: list[dict[str, Any]]) -> str:
    headers = (
        "route_id",
        "status",
        "reuses_in_repo",
        "next_lemma",
        "clay_promoted",
        "rank",
    )
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
                    row["status"],
                    row["reuses_in_repo"],
                    row["next_lemma"],
                    str(row["clay_promoted"]).lower(),
                    str(row["recommendation_rank"]),
                )
            )
            + " |"
        )
    return "\n".join(lines)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    recommended = min(rows, key=lambda row: row["recommendation_rank"])
    any_clay_complete = any(row["complete"] and row["clay"] for row in rows)
    return {
        "contract": CONTRACT,
        "route_count": len(rows),
        "candidate_routes": [row["route_id"] for row in rows],
        "recommended_next_route": recommended["route_id"],
        "next_lemma": recommended["next_lemma"],
        "complete": any_clay_complete,
        "clay": any_clay_complete,
        "clay_promoted": False,
        "clay_navier_stokes_promoted": False,
        "recommended_status": recommended["status"],
        "blocked_route_count": sum(
            1
            for row in rows
            if row["status"].startswith("blocked") or row["status"] == "obstructed"
        ),
        "open_route_count": sum(1 for row in rows if row["status"].startswith("open")),
        "exit_code": 1,
        "exit_reason": "no Clay-complete route after post-Crow pivot classification",
    }


def write_report(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    text = "\n".join(
        (
            f"# {CONTRACT}",
            "",
            "Deterministic classifier for post-Crow Navier-Stokes route choices.",
            "",
            f"Recommended next route: {summary['recommended_next_route']}",
            f"Next lemma: {summary['next_lemma']}",
            f"Complete: {str(summary['complete']).lower()}",
            f"Clay: {str(summary['clay']).lower()}",
            "",
            "Exit status: 1 because no candidate route is Clay-complete.",
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

    rows = [choice.row() for choice in route_choices()]
    summary = build_summary(rows)

    write_json(out_dir / ROWS_NAME, rows)
    write_json(out_dir / SUMMARY_NAME, summary)
    write_csv(out_dir / CSV_NAME, rows)
    write_report(out_dir / REPORT_NAME, summary, rows)

    return 1


if __name__ == "__main__":
    sys.exit(main())
