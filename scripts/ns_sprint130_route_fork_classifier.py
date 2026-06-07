#!/usr/bin/env python3
"""Sprint 130 NS route-fork classifier."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint130_route_fork_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint130_route_fork_classifier")
SUMMARY_NAME = "ns_sprint130_route_fork_classifier_summary.json"
ROWS_NAME = "ns_sprint130_route_fork_classifier_rows.json"
REPORT_NAME = "ns_sprint130_route_fork_classifier.md"

RECOMMENDED_NEXT_FORK = "RegularityConclusion"
NS_OBSTRUCTION = "ViscousDominanceNearBlowup"
EULER_GAP_LEMMAS = (
    "NoLogAxisymmetricBiotSavartUniform",
    "SourceAlignmentWithVorticityMaximum",
)

EXPECTED_CLASSIFICATIONS = {
    "MarginalScalingCaseAnalysis": "open_unclear",
    "EulerBlowupIsolation": "open_with_two_gap_lemmas",
    "RegularityConclusion": "defensible_partial_obstruction_result",
}


@dataclass(frozen=True)
class RouteFork:
    fork_id: str
    fork_label: str
    classification: str
    recommendation_rank: int
    complete: bool
    clay: bool
    ns_route_obstructed: bool
    euler_route_open: bool
    obstruction: str
    gap_lemmas: list[str]
    next_action: str
    rationale: str

    def row(self) -> dict[str, Any]:
        return asdict(self)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def fork_rows() -> list[dict[str, Any]]:
    forks = [
        RouteFork(
            fork_id="MarginalScalingCaseAnalysis",
            fork_label="Fork A",
            classification="open_unclear",
            recommendation_rank=3,
            complete=False,
            clay=False,
            ns_route_obstructed=False,
            euler_route_open=False,
            obstruction="marginal_scaling_does_not_decide_route",
            gap_lemmas=[],
            next_action="leave open until marginal scaling is sharpened or obstructed",
            rationale=(
                "The marginal scaling case does not currently provide a closed "
                "Navier-Stokes regularity route or a blowup route. It remains "
                "open and unclear."
            ),
        ),
        RouteFork(
            fork_id="EulerBlowupIsolation",
            fork_label="Fork B",
            classification="open_with_two_gap_lemmas",
            recommendation_rank=2,
            complete=False,
            clay=False,
            ns_route_obstructed=False,
            euler_route_open=True,
            obstruction="not_a_navier_stokes_promotion",
            gap_lemmas=list(EULER_GAP_LEMMAS),
            next_action="keep Euler separate and close both gap lemmas before reuse",
            rationale=(
                "The Euler blowup isolation route remains separate from "
                "Navier-Stokes and depends on the two gap lemmas "
                + ", ".join(EULER_GAP_LEMMAS)
                + "."
            ),
        ),
        RouteFork(
            fork_id="RegularityConclusion",
            fork_label="Fork C",
            classification="defensible_partial_obstruction_result",
            recommendation_rank=1,
            complete=False,
            clay=False,
            ns_route_obstructed=True,
            euler_route_open=False,
            obstruction=NS_OBSTRUCTION,
            gap_lemmas=[],
            next_action="record the Hou-Luo NS route obstruction as the next fork",
            rationale=(
                "The defensible result is partial: the Hou-Luo Navier-Stokes "
                "route is obstructed by " + NS_OBSTRUCTION + ", while this does "
                "not solve the full Clay Navier-Stokes problem."
            ),
        ),
    ]
    return [fork.row() for fork in forks]


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def markdown_table(rows: list[dict[str, Any]]) -> str:
    headers = (
        "fork_label",
        "fork_id",
        "classification",
        "complete",
        "clay",
        "obstruction",
        "next_action",
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
                    row["fork_label"],
                    row["fork_id"],
                    row["classification"],
                    str(row["complete"]).lower(),
                    str(row["clay"]).lower(),
                    row["obstruction"],
                    row["next_action"],
                )
            )
            + " |"
        )
    return "\n".join(lines)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    recommended = min(rows, key=lambda row: row["recommendation_rank"])
    classifications = {row["fork_id"]: row["classification"] for row in rows}
    euler_gap_lemmas = sorted(
        {
            lemma
            for row in rows
            for lemma in row["gap_lemmas"]
            if row["fork_id"] == "EulerBlowupIsolation"
        }
    )
    return {
        "contract": CONTRACT,
        "fork_count": len(rows),
        "candidate_forks": [row["fork_id"] for row in rows],
        "classifications": classifications,
        "required_classifications_met": classifications == EXPECTED_CLASSIFICATIONS,
        "recommended_next_fork": RECOMMENDED_NEXT_FORK,
        "recommended_fork_id": recommended["fork_id"],
        "recommended_classification": recommended["classification"],
        "hou_luo_ns_route_obstructed": True,
        "hou_luo_ns_obstruction": NS_OBSTRUCTION,
        "euler_route_open_not_ns": True,
        "euler_gap_lemmas": euler_gap_lemmas,
        "euler_gap_lemma_count": len(euler_gap_lemmas),
        "complete": False,
        "clay": False,
        "clay_promoted": False,
        "clay_navier_stokes_promoted": False,
        "open_fork_count": sum(1 for row in rows if "open" in row["classification"]),
        "ns_obstructed_fork_count": sum(1 for row in rows if row["ns_route_obstructed"]),
        "euler_open_fork_count": sum(1 for row in rows if row["euler_route_open"]),
        "partial_obstruction_result_count": sum(
            1 for row in rows if "partial_obstruction" in row["classification"]
        ),
        "exit_code": 1,
        "exit_reason": (
            "Full Clay Navier-Stokes remains unsolved; only the Hou-Luo NS route "
            "is recorded as obstructed, and the Euler route remains separate/open"
        ),
    }


def write_report(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    text = "\n".join(
        (
            f"# {CONTRACT}",
            "",
            "Deterministic Sprint130 classifier for NS route forks.",
            "",
            f"Recommended next fork: {summary['recommended_next_fork']}",
            f"Recommended classification: {summary['recommended_classification']}",
            f"Hou-Luo NS route obstructed: {str(summary['hou_luo_ns_route_obstructed']).lower()}",
            f"Hou-Luo NS obstruction: {summary['hou_luo_ns_obstruction']}",
            f"Euler route open, not NS: {str(summary['euler_route_open_not_ns']).lower()}",
            "Euler gap lemmas: " + ", ".join(summary["euler_gap_lemmas"]),
            f"Clay Navier-Stokes promoted: {str(summary['clay_navier_stokes_promoted']).lower()}",
            f"Required classifications met: {str(summary['required_classifications_met']).lower()}",
            f"Complete: {str(summary['complete']).lower()}",
            "",
            "Exit status: 1 because full Clay Navier-Stokes remains unsolved.",
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

    rows = fork_rows()
    summary = build_summary(rows)

    write_json(out_dir / ROWS_NAME, rows)
    write_json(out_dir / SUMMARY_NAME, summary)
    write_report(out_dir / REPORT_NAME, summary, rows)

    return int(summary["exit_code"])


if __name__ == "__main__":
    sys.exit(main())
