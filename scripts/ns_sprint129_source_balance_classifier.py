#!/usr/bin/env python3
"""Sprint 129 NS source-balance classifier."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint129_source_balance_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint129_source_balance_classifier")
SUMMARY_NAME = "ns_sprint129_source_balance_classifier_summary.json"
ROWS_NAME = "ns_sprint129_source_balance_classifier_rows.json"
REPORT_NAME = "ns_sprint129_source_balance_classifier.md"

SOURCE_BALANCE = "partial_z(u1^2)=2 u1 partial_z u1"
RECOMMENDED_NEXT_LEMMA = "AdvectiveConcentrationVsDiffusionBound"

EXPECTED_CLASSIFICATIONS = {
    "lower_bound_closes": "formal_identity_lower_bound",
    "lower_bound_missing": "open_required",
    "diffusion_dominates": "obstruction",
    "advective_concentration_formal": "formal_primary_open",
    "source_collapse_obstruction": "obstruction_primary",
}


@dataclass(frozen=True)
class SourceBalanceScenario:
    scenario_id: str
    classification: str
    u1_ratio_to_omega: str
    gradient_tracks_omega: bool
    source_scales_quadratic: bool
    bkm_blowup_route: bool
    obstruction: str
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


def scenario_rows() -> list[dict[str, Any]]:
    scenarios = [
        SourceBalanceScenario(
            scenario_id="lower_bound_closes",
            classification="formal_identity_lower_bound",
            u1_ratio_to_omega="comparable",
            gradient_tracks_omega=True,
            source_scales_quadratic=True,
            bkm_blowup_route=True,
            obstruction="none_inside_formal_lower_bound",
            clay_promoted=False,
            next_action="use only as the formal target case",
            rationale=(
                "If u1 remains comparable to omega and partial_z u1 tracks the "
                "vorticity scale, the identity " + SOURCE_BALANCE + " gives a "
                "quadratic source compatible with a BKM route. This is a target "
                "case, not an established unconditional estimate."
            ),
        ),
        SourceBalanceScenario(
            scenario_id="lower_bound_missing",
            classification="open_required",
            u1_ratio_to_omega="uncontrolled",
            gradient_tracks_omega=False,
            source_scales_quadratic=False,
            bkm_blowup_route=False,
            obstruction="missing_lower_bound_for_u1_and_partial_z_u1",
            clay_promoted=False,
            next_action="prove or obstruct " + RECOMMENDED_NEXT_LEMMA,
            rationale=(
                "The source identity is exact, but it does not provide a lower "
                "bound unless u1 and partial_z u1 are tied to the concentrating "
                "vorticity scale."
            ),
        ),
        SourceBalanceScenario(
            scenario_id="diffusion_dominates",
            classification="obstruction",
            u1_ratio_to_omega="subcritical",
            gradient_tracks_omega=False,
            source_scales_quadratic=False,
            bkm_blowup_route=False,
            obstruction="diffusion_outweighs_advective_source",
            clay_promoted=False,
            next_action="record as obstruction to source dominance",
            rationale=(
                "When diffusion controls the candidate concentration scale, the "
                "quadratic formal source is not enough to force a BKM-divergent "
                "growth route."
            ),
        ),
        SourceBalanceScenario(
            scenario_id="advective_concentration_formal",
            classification="formal_primary_open",
            u1_ratio_to_omega="comparable_assumed",
            gradient_tracks_omega=True,
            source_scales_quadratic=True,
            bkm_blowup_route=True,
            obstruction="requires_advective_concentration_vs_diffusion_bound",
            clay_promoted=False,
            next_action="prove or obstruct " + RECOMMENDED_NEXT_LEMMA,
            rationale=(
                "The concentration scenario is the live formal route: the exact "
                "product derivative supplies the desired quadratic source only "
                "after advection is shown to beat the diffusive bound."
            ),
        ),
        SourceBalanceScenario(
            scenario_id="source_collapse_obstruction",
            classification="obstruction_primary",
            u1_ratio_to_omega="collapses",
            gradient_tracks_omega=False,
            source_scales_quadratic=False,
            bkm_blowup_route=False,
            obstruction="u1_or_gradient_collapse_kills_quadratic_source",
            clay_promoted=False,
            next_action="treat as the decisive obstruction alternative",
            rationale=(
                "If u1 or partial_z u1 collapses relative to omega, the exact "
                "identity remains true but the source loses the quadratic size "
                "needed for the proposed BKM blowup route."
            ),
        ),
    ]
    return [scenario.row() for scenario in scenarios]


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def markdown_table(rows: list[dict[str, Any]]) -> str:
    headers = (
        "scenario_id",
        "classification",
        "u1_ratio_to_omega",
        "gradient_tracks_omega",
        "source_scales_quadratic",
        "bkm_blowup_route",
        "clay_promoted",
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
                    row["scenario_id"],
                    row["classification"],
                    row["u1_ratio_to_omega"],
                    str(row["gradient_tracks_omega"]).lower(),
                    str(row["source_scales_quadratic"]).lower(),
                    str(row["bkm_blowup_route"]).lower(),
                    str(row["clay_promoted"]).lower(),
                    row["next_action"],
                )
            )
            + " |"
        )
    return "\n".join(lines)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    classifications = {row["scenario_id"]: row["classification"] for row in rows}
    clay_promoted = any(row["clay_promoted"] for row in rows)
    return {
        "contract": CONTRACT,
        "source_balance": SOURCE_BALANCE,
        "scenario_count": len(rows),
        "candidate_scenarios": [row["scenario_id"] for row in rows],
        "classifications": classifications,
        "required_classifications_met": classifications == EXPECTED_CLASSIFICATIONS,
        "recommended_next_lemma": RECOMMENDED_NEXT_LEMMA,
        "recommended_action": "prove_or_obstruct_" + RECOMMENDED_NEXT_LEMMA,
        "primary_open_scenario": "advective_concentration_formal",
        "primary_obstruction_scenario": "source_collapse_obstruction",
        "formal_lower_bound_scenario": "lower_bound_closes",
        "complete": False,
        "clay": False,
        "clay_promoted": False,
        "clay_navier_stokes_promoted": False,
        "row_clay_promoted_any": clay_promoted,
        "quadratic_source_scenario_count": sum(
            1 for row in rows if row["source_scales_quadratic"]
        ),
        "bkm_route_scenario_count": sum(1 for row in rows if row["bkm_blowup_route"]),
        "obstruction_count": sum(1 for row in rows if row["obstruction"] != "none_inside_formal_lower_bound"),
        "exit_code": 1,
        "exit_reason": (
            "NS is incomplete; AdvectiveConcentrationVsDiffusionBound must be "
            "proved or obstructed, and Clay is not promoted"
        ),
    }


def write_report(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    text = "\n".join(
        (
            f"# {CONTRACT}",
            "",
            "Deterministic Sprint129 classifier for the NS source balance.",
            "",
            f"Source balance: {summary['source_balance']}",
            f"Recommended next lemma: {summary['recommended_next_lemma']}",
            f"Recommended action: {summary['recommended_action']}",
            f"Primary open scenario: {summary['primary_open_scenario']}",
            f"Primary obstruction scenario: {summary['primary_obstruction_scenario']}",
            f"Required classifications met: {str(summary['required_classifications_met']).lower()}",
            f"Clay promoted: {str(summary['clay_promoted']).lower()}",
            "",
            (
                "Exit status: 1 because the advective concentration versus "
                "diffusion bound remains unresolved and Clay is not promoted."
            ),
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

    rows = scenario_rows()
    summary = build_summary(rows)

    write_json(out_dir / ROWS_NAME, rows)
    write_json(out_dir / SUMMARY_NAME, summary)
    write_report(out_dir / REPORT_NAME, summary, rows)

    return 1


if __name__ == "__main__":
    sys.exit(main())
