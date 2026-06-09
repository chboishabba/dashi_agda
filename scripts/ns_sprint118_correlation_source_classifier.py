#!/usr/bin/env python3
"""Sprint 118 NS correlation source classifier."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint118_correlation_source_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint118_correlation_source_classifier")
SUMMARY_NAME = "ns_sprint118_correlation_source_classifier_summary.json"
ROWS_NAME = "ns_sprint118_correlation_source_classifier_rows.json"
REPORT_NAME = "ns_sprint118_correlation_source_classifier.md"

RECOMMENDED_SOURCE = "PersistentAlignmentExistence"
OPEN_GATE = "NonCircularGeometricCorrelationSource"


@dataclass(frozen=True)
class CorrelationSource:
    source_id: str
    classification: str
    recommendation_rank: int
    complete: bool
    clay: bool
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


def source_rows() -> list[dict[str, Any]]:
    sources = [
        CorrelationSource(
            source_id="kinematic_compressive_alignment_condition",
            classification="conditional_sign_closed_not_source",
            recommendation_rank=5,
            complete=False,
            clay=False,
            clay_promoted=False,
            next_action="use only as a conditional sign lemma",
            rationale=(
                "The compressive alignment condition closes the sign after the "
                "condition is granted, but it does not derive the condition from "
                "unforced Leray-admissible Navier-Stokes evolution."
            ),
        ),
        CorrelationSource(
            source_id="persistent_alignment_existence",
            classification="open_primary_gate",
            recommendation_rank=1,
            complete=False,
            clay=False,
            clay_promoted=False,
            next_action="prove " + RECOMMENDED_SOURCE,
            rationale=(
                "This is the primary source target because it would derive a "
                "persistent non-circular alignment mechanism rather than assuming "
                "the correlation needed by the transfer sign."
            ),
        ),
        CorrelationSource(
            source_id="leray_energy_class",
            classification="magnitude_only_no_sign_source",
            recommendation_rank=6,
            complete=False,
            clay=False,
            clay_promoted=False,
            next_action="retain as admissibility bookkeeping",
            rationale=(
                "The Leray energy class supplies magnitude and compactness control, "
                "but it does not determine the high-high to low-mode sign."
            ),
        ),
        CorrelationSource(
            source_id="concentration_geometry",
            classification="closed_by_sprint117",
            recommendation_rank=7,
            complete=False,
            clay=False,
            clay_promoted=False,
            next_action="do not reopen without a new independent mechanism",
            rationale=(
                "Sprint117 closed the concentration-only route because geometry "
                "and concentration accounting did not independently supply the "
                "needed non-circular source."
            ),
        ),
        CorrelationSource(
            source_id="imposed_alignment_assumption",
            classification="rejected_circular",
            recommendation_rank=8,
            complete=False,
            clay=False,
            clay_promoted=False,
            next_action="exclude from promotion accounting",
            rationale=(
                "Imposing the alignment inserts the target correlation and is "
                "therefore circular for a Clay-level Navier-Stokes route."
            ),
        ),
        CorrelationSource(
            source_id="option_a_global_sign_nonpositivity",
            classification="open_alternative",
            recommendation_rank=2,
            complete=False,
            clay=False,
            clay_promoted=False,
            next_action="compare after the primary persistence gate is tested",
            rationale=(
                "A global sign nonpositivity proof remains an alternative regular "
                "route, but it is less direct than deriving persistent alignment."
            ),
        ),
        CorrelationSource(
            source_id="burgers_vortex_concentration",
            classification="open_secondary_comparison",
            recommendation_rank=3,
            complete=False,
            clay=False,
            clay_promoted=False,
            next_action="hold as a secondary model comparison",
            rationale=(
                "The Burgers vortex lane can compare concentration heuristics "
                "against the primary source gate, but it does not yet supply a "
                "general unforced sign source."
            ),
        ),
    ]
    return [source.row() for source in sources]


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def markdown_table(rows: list[dict[str, Any]]) -> str:
    headers = ("source_id", "classification", "complete", "clay", "next_action")
    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    for row in rows:
        lines.append(
            "| "
            + " | ".join(
                (
                    row["source_id"],
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
    clay_complete = any(row["complete"] and row["clay"] for row in rows)
    return {
        "contract": CONTRACT,
        "source_count": len(rows),
        "candidate_sources": [row["source_id"] for row in rows],
        "classifications": {row["source_id"]: row["classification"] for row in rows},
        "recommended_source": RECOMMENDED_SOURCE,
        "recommended_source_id": recommended["source_id"],
        "recommended_classification": recommended["classification"],
        "open_gate": OPEN_GATE,
        "non_circular_geometric_correlation_source": "open",
        "complete": clay_complete,
        "clay": clay_complete,
        "clay_promoted": False,
        "clay_navier_stokes_promoted": False,
        "open_source_count": sum(
            1 for row in rows if row["classification"].startswith("open")
        ),
        "rejected_source_count": sum(
            1 for row in rows if row["classification"].startswith("rejected")
        ),
        "exit_code": 1,
        "exit_reason": "no Clay-complete source",
    }


def write_report(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    text = "\n".join(
        (
            f"# {CONTRACT}",
            "",
            "Deterministic Sprint118 classifier for Navier-Stokes correlation sources.",
            "",
            f"Recommended source: {summary['recommended_source']}",
            f"Recommended source id: {summary['recommended_source_id']}",
            f"Open gate: {summary['open_gate']}",
            "NonCircularGeometricCorrelationSource remains open.",
            f"Complete: {str(summary['complete']).lower()}",
            f"Clay: {str(summary['clay']).lower()}",
            "",
            "Exit status: 1 because no Clay-complete source exists.",
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

    rows = source_rows()
    summary = build_summary(rows)

    write_json(out_dir / ROWS_NAME, rows)
    write_json(out_dir / SUMMARY_NAME, summary)
    write_report(out_dir / REPORT_NAME, summary, rows)

    return 1


if __name__ == "__main__":
    sys.exit(main())
