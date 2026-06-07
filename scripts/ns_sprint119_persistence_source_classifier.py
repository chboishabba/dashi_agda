#!/usr/bin/env python3
"""Sprint 119 NS persistence source classifier."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint119_persistence_source_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint119_persistence_source_classifier")
SUMMARY_NAME = "ns_sprint119_persistence_source_classifier_summary.json"
ROWS_NAME = "ns_sprint119_persistence_source_classifier_rows.json"
REPORT_NAME = "ns_sprint119_persistence_source_classifier.md"

RECOMMENDED_NEXT_LEMMA = "PersistentAlignmentExistenceLowerBound"
PRIMARY_GATE = "persistent_alignment_existence"


@dataclass(frozen=True)
class PersistenceSource:
    mechanism_id: str
    classification: str
    recommendation_rank: int
    non_circular_source: bool
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


def source_rows() -> list[dict[str, Any]]:
    sources = [
        PersistenceSource(
            mechanism_id="persistent_alignment_existence",
            classification="open_primary_gate",
            recommendation_rank=1,
            non_circular_source=False,
            complete=False,
            clay=False,
            next_action="prove " + RECOMMENDED_NEXT_LEMMA,
            rationale=(
                "This is the primary gate because a lower bound on persistent "
                "alignment would supply the missing duration source without "
                "assuming the transfer sign."
            ),
        ),
        PersistenceSource(
            mechanism_id="hyperbolic_strain_template",
            classification="open_requires_construction",
            recommendation_rank=2,
            non_circular_source=False,
            complete=False,
            clay=False,
            next_action="construct an admissible template and persistence estimate",
            rationale=(
                "Hyperbolic strain has the right local shape, but the classifier "
                "does not find an unforced Leray-admissible construction with the "
                "needed persistence lower bound."
            ),
        ),
        PersistenceSource(
            mechanism_id="beltrami_wave_packet_alignment",
            classification="open_secondary",
            recommendation_rank=3,
            non_circular_source=False,
            complete=False,
            clay=False,
            next_action="keep as a secondary comparison mechanism",
            rationale=(
                "Beltrami wave packets can model alignment, but they have not been "
                "connected to a general non-circular persistence source."
            ),
        ),
        PersistenceSource(
            mechanism_id="local_smooth_continuation",
            classification="short_time_conditional_not_global_source",
            recommendation_rank=4,
            non_circular_source=False,
            complete=False,
            clay=False,
            next_action="use only for conditional short-time propagation",
            rationale=(
                "Local smooth continuation can propagate a supplied smooth state "
                "for short time, but it does not establish a global persistence "
                "source from Leray-class data."
            ),
        ),
        PersistenceSource(
            mechanism_id="leray_energy_bounds",
            classification="magnitude_only_no_alignment_duration",
            recommendation_rank=5,
            non_circular_source=False,
            complete=False,
            clay=False,
            next_action="retain as magnitude bookkeeping",
            rationale=(
                "Leray energy bounds control size and admissibility, but they do "
                "not give the alignment direction or the duration lower bound."
            ),
        ),
        PersistenceSource(
            mechanism_id="numerical_vortex_alignment",
            classification="empirical_not_proof",
            recommendation_rank=6,
            non_circular_source=False,
            complete=False,
            clay=False,
            next_action="treat as heuristic evidence only",
            rationale=(
                "Numerical vortex alignment may guide examples, but empirical "
                "evidence is not a proof of a Clay-level persistence source."
            ),
        ),
        PersistenceSource(
            mechanism_id="imposed_alignment_assumption",
            classification="rejected_circular",
            recommendation_rank=7,
            non_circular_source=False,
            complete=False,
            clay=False,
            next_action="exclude from source accounting",
            rationale=(
                "Imposing alignment inserts the condition that must be derived, so "
                "it is circular for the persistence-source route."
            ),
        ),
    ]
    return [source.row() for source in sources]


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def markdown_table(rows: list[dict[str, Any]]) -> str:
    headers = (
        "mechanism_id",
        "classification",
        "non_circular_source",
        "complete",
        "clay",
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
                    row["mechanism_id"],
                    row["classification"],
                    str(row["non_circular_source"]).lower(),
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
    complete = any(row["complete"] and row["clay"] for row in rows)
    non_circular_source_established = any(row["non_circular_source"] for row in rows)
    return {
        "contract": CONTRACT,
        "mechanism_count": len(rows),
        "candidate_mechanisms": [row["mechanism_id"] for row in rows],
        "classifications": {
            row["mechanism_id"]: row["classification"] for row in rows
        },
        "recommended_next_lemma": RECOMMENDED_NEXT_LEMMA,
        "recommended_mechanism_id": recommended["mechanism_id"],
        "recommended_classification": recommended["classification"],
        "primary_gate": PRIMARY_GATE,
        "non_circular_source_established": non_circular_source_established,
        "complete": complete,
        "clay": complete,
        "clay_promoted": False,
        "clay_navier_stokes_promoted": False,
        "open_mechanism_count": sum(
            1 for row in rows if row["classification"].startswith("open")
        ),
        "rejected_mechanism_count": sum(
            1 for row in rows if row["classification"].startswith("rejected")
        ),
        "exit_code": 1,
        "exit_reason": "no non-circular persistence source established",
    }


def write_report(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    text = "\n".join(
        (
            f"# {CONTRACT}",
            "",
            "Deterministic Sprint119 classifier for Navier-Stokes persistence sources.",
            "",
            f"Recommended next lemma: {summary['recommended_next_lemma']}",
            f"Recommended mechanism id: {summary['recommended_mechanism_id']}",
            f"Primary gate: {summary['primary_gate']}",
            "Non-circular source established: false",
            f"Complete: {str(summary['complete']).lower()}",
            f"Clay: {str(summary['clay']).lower()}",
            "",
            "Exit status: 1 because no non-circular persistence source is established.",
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
