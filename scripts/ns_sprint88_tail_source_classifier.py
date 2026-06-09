#!/usr/bin/env python3
"""Sprint 88 NS H1-tail source classifier.

Classifies candidate sources for the danger-shell pointwise absorption input.
The promotion rule is deliberately fail-closed: a source is sufficient only if
it supplies both a pointwise-in-time H1 tail and an independent epsilon
coefficient for the absorption inequality.
"""

from __future__ import annotations

import argparse
import csv
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint88_tail_source_classifier"
ROUTE_OPEN = "NS_SPRINT88_TAIL_SOURCE_CLASSIFIER_OPEN"
SUMMARY_NAME = "ns_sprint88_tail_source_classifier_summary.json"
SOURCE_TABLE = "ns_sprint88_tail_source_classifier_sources.csv"
GATE_TABLE = "ns_sprint88_tail_source_classifier_gate_table.csv"
REPORT_NAME = "ns_sprint88_tail_source_classifier_report.md"


@dataclass(frozen=True)
class CandidateSource:
    source_id: str
    source_name: str
    source_kind: str
    source_path: str
    required_anchor: str
    supplied_tail_norm: str
    tail_time_type: str
    supplies_pointwise_h1_tail: bool
    supplies_independent_epsilon_coefficient: bool
    coefficient_status: str
    circularity_risk: str
    classification: str
    reason: str
    next_required_input: str

    @property
    def sufficient_for_pointwise_absorption(self) -> bool:
        return (
            self.supplies_pointwise_h1_tail
            and self.supplies_independent_epsilon_coefficient
        )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    return parser.parse_args()


def candidate_sources() -> list[CandidateSource]:
    return [
        CandidateSource(
            source_id="T1",
            source_name="KStarL2Tail",
            source_kind="tail_smallness",
            source_path="DASHI/Physics/Closure/NSSprint86KStarHHalfTailObstructionReceipt.agda",
            required_anchor="kstarAdmissibilityAloneControlsHHalfTailDerivedInRepo",
            supplied_tail_norm="L2 tail at KStar scale",
            tail_time_type="candidate pointwise scale statement, but below H1",
            supplies_pointwise_h1_tail=False,
            supplies_independent_epsilon_coefficient=False,
            coefficient_status="missing epsilon<1 absorption coefficient",
            circularity_risk="low as an obstruction record; insufficient regularity strength",
            classification="INSUFFICIENT_L2_NOT_H1",
            reason=(
                "L2 tail control does not supply the pointwise H1 tail required "
                "by the danger-shell absorption scalar."
            ),
            next_required_input="pointwise H1 tail upgrade independent of absorption",
        ),
        CandidateSource(
            source_id="T2",
            source_name="LerayEnergyPointwise",
            source_kind="energy_bound",
            source_path="DASHI/Physics/Closure/NSCarrierEnergyInequalityReceipt.agda",
            required_anchor="NSCarrierEnergyInequalityReceipt",
            supplied_tail_norm="global L2 energy / weak energy inequality",
            tail_time_type="pointwise L2 energy, not pointwise H1 tail",
            supplies_pointwise_h1_tail=False,
            supplies_independent_epsilon_coefficient=False,
            coefficient_status="no independent epsilon absorption margin",
            circularity_risk="moderate if upgraded through hidden regularity",
            classification="INSUFFICIENT_ENERGY_LEVEL_ONLY",
            reason=(
                "Leray energy is too weak for the H1 danger-shell tail and "
                "does not provide a small absorption coefficient."
            ),
            next_required_input="non-circular enstrophy/H1 tail localization theorem",
        ),
        CandidateSource(
            source_id="T3",
            source_name="TimeIntegratedDissipation",
            source_kind="dissipation_integral",
            source_path="DASHI/Physics/Closure/NSDissipationCutoffReceipt.agda",
            required_anchor="NSDissipationCutoffReceipt",
            supplied_tail_norm="time-integrated H1/dissipation budget",
            tail_time_type="integrated in time, not pointwise at danger time",
            supplies_pointwise_h1_tail=False,
            supplies_independent_epsilon_coefficient=False,
            coefficient_status="averaged budget does not yield pointwise epsilon",
            circularity_risk="moderate; pointwise extraction needs additional measure/continuity input",
            classification="INSUFFICIENT_TIME_INTEGRATED",
            reason=(
                "A time-integrated dissipation estimate cannot by itself certify "
                "the pointwise H1 tail at the selected danger shell."
            ),
            next_required_input="pointwise-in-time extraction with independent small coefficient",
        ),
        CandidateSource(
            source_id="T4",
            source_name="DangerShellLocalMechanism",
            source_kind="localized_mechanism",
            source_path="DASHI/Physics/Closure/NSSprint87DangerShellSupFactorizationReceipt.agda",
            required_anchor="dangerShellAbsorptionConditionClosed",
            supplied_tail_norm="localized danger-shell H1 tail target",
            tail_time_type="pointwise target named, not proved closed",
            supplies_pointwise_h1_tail=False,
            supplies_independent_epsilon_coefficient=False,
            coefficient_status="absorption condition recorded open",
            circularity_risk="high if tail is derived from the same absorption inequality",
            classification="TARGET_NOT_SOURCE",
            reason=(
                "The local mechanism names the correct pointwise target but does "
                "not independently supply the H1 tail or epsilon coefficient."
            ),
            next_required_input="prove local mechanism without reusing absorption conclusion",
        ),
        CandidateSource(
            source_id="T5",
            source_name="CriticalCoefficientSmallness",
            source_kind="coefficient_margin",
            source_path="scripts/ns_sprint87_absorption_scaling_audit.py",
            required_anchor="SCALAR_CONDITION",
            supplied_tail_norm="critical coefficient condition only",
            tail_time_type="coefficient-side scalar condition",
            supplies_pointwise_h1_tail=False,
            supplies_independent_epsilon_coefficient=False,
            coefficient_status="epsilon criterion named, independent value not supplied",
            circularity_risk="low as a gate; insufficient without tail input",
            classification="INSUFFICIENT_COEFFICIENT_ONLY",
            reason=(
                "Critical coefficient smallness can close only after a pointwise "
                "H1 tail is supplied, and no independent epsilon value is present."
            ),
            next_required_input="independent coefficient bound plus pointwise H1 tail source",
        ),
    ]


def source_rows(repo_root: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for source in candidate_sources():
        row = asdict(source)
        path = repo_root / source.source_path
        text = path.read_text(encoding="utf-8") if path.exists() else ""
        row.update(
            {
                "present_in_repo": path.exists(),
                "required_anchor_present": bool(text and source.required_anchor in text),
                "sufficient_for_pointwise_absorption": source.sufficient_for_pointwise_absorption,
                "route_decision": ROUTE_OPEN,
            }
        )
        rows.append(row)
    return rows


def gate_rows(sources: list[dict[str, Any]]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for source in sources:
        has_tail = bool(source["supplies_pointwise_h1_tail"])
        has_epsilon = bool(source["supplies_independent_epsilon_coefficient"])
        sufficient = bool(source["sufficient_for_pointwise_absorption"])
        if sufficient:
            status = "SUFFICIENT_RECORDED"
        elif not has_tail and not has_epsilon:
            status = "FAIL_CLOSED_MISSING_TAIL_AND_EPSILON"
        elif not has_tail:
            status = "FAIL_CLOSED_MISSING_POINTWISE_H1_TAIL"
        else:
            status = "FAIL_CLOSED_MISSING_INDEPENDENT_EPSILON"
        rows.append(
            {
                "gate_id": source["source_id"],
                "source_name": source["source_name"],
                "requires_pointwise_h1_tail": True,
                "requires_independent_epsilon_coefficient": True,
                "supplies_pointwise_h1_tail": has_tail,
                "supplies_independent_epsilon_coefficient": has_epsilon,
                "sufficient_for_pointwise_absorption": sufficient,
                "status": status,
                "classification": source["classification"],
                "next_required_input": source["next_required_input"],
                "route_decision": ROUTE_OPEN,
            }
        )
    rows.append(
        {
            "gate_id": "G_ALL",
            "source_name": "AnyCandidateSourceSufficient",
            "requires_pointwise_h1_tail": True,
            "requires_independent_epsilon_coefficient": True,
            "supplies_pointwise_h1_tail": any(
                row["supplies_pointwise_h1_tail"] for row in sources
            ),
            "supplies_independent_epsilon_coefficient": any(
                row["supplies_independent_epsilon_coefficient"] for row in sources
            ),
            "sufficient_for_pointwise_absorption": any(
                row["sufficient_for_pointwise_absorption"] for row in sources
            ),
            "status": "FALSE_NO_CANDIDATE_SUPPLIES_BOTH_REQUIREMENTS",
            "classification": "NO_SUFFICIENT_SOURCE",
            "next_required_input": (
                "single non-circular source supplying pointwise H1 tail and "
                "independent epsilon coefficient"
            ),
            "route_decision": ROUTE_OPEN,
        }
    )
    return rows


def summary_payload(sources: list[dict[str, Any]]) -> dict[str, Any]:
    sufficient_sources = [
        row["source_name"]
        for row in sources
        if row["sufficient_for_pointwise_absorption"]
    ]
    return {
        "contract": CONTRACT,
        "complete": False,
        "route_decision": ROUTE_OPEN,
        "source_table": SOURCE_TABLE,
        "gate_table": GATE_TABLE,
        "report": REPORT_NAME,
        "candidate_source_names": [row["source_name"] for row in sources],
        "candidate_count": len(sources),
        "source_count": len(sources),
        "sufficient_source_count": len(sufficient_sources),
        "sufficient_sources": sufficient_sources,
        "sufficient_for_pointwise_absorption": bool(sufficient_sources),
        "pointwise_absorption_rule": (
            "sufficient iff one source supplies pointwise H1 tail and an "
            "independent epsilon coefficient"
        ),
        "requires_pointwise_h1_tail": True,
        "requires_independent_epsilon_coefficient": True,
        "all_candidates_fail_closed": not sufficient_sources,
        "unconditional_closure": False,
        "clay_navier_stokes_promoted": False,
        "clay_promotion_recorded_false": True,
        "next_required_gate": "PointwiseH1TailWithIndependentEpsilonCoefficient",
        "open_obligations": [
            "derive pointwise H1 tail at the danger shell from non-circular NS inputs",
            "derive an independent epsilon<1 absorption coefficient",
            "verify the tail and coefficient are not obtained from the target absorption inequality",
        ],
    }


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def markdown(summary: dict[str, Any], sources: list[dict[str, Any]], gates: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 88 Tail Source Classifier",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Route: `{summary['route_decision']}`",
        f"- Sufficient for pointwise absorption: `{summary['sufficient_for_pointwise_absorption']}`",
        f"- Rule: {summary['pointwise_absorption_rule']}",
        "",
        "## Source Classification",
        "",
        "| Source | Pointwise H1 tail | Independent epsilon | Sufficient | Classification |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in sources:
        lines.append(
            f"| `{row['source_name']}` | `{row['supplies_pointwise_h1_tail']}` | "
            f"`{row['supplies_independent_epsilon_coefficient']}` | "
            f"`{row['sufficient_for_pointwise_absorption']}` | "
            f"`{row['classification']}` |"
        )
    lines.extend(["", "## Gates", "", "| Gate | Status | Next input |", "| --- | --- | --- |"])
    for row in gates:
        lines.append(
            f"| `{row['source_name']}` | `{row['status']}` | {row['next_required_input']} |"
        )
    lines.extend(["", "## Open Obligations", ""])
    lines.extend(f"- {item}" for item in summary["open_obligations"])
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    args = parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    sources = source_rows(args.repo_root)
    gates = gate_rows(sources)
    summary = summary_payload(sources)

    write_csv(args.out_dir / SOURCE_TABLE, sources)
    write_csv(args.out_dir / GATE_TABLE, gates)
    (args.out_dir / SUMMARY_NAME).write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    (args.out_dir / REPORT_NAME).write_text(
        markdown(summary, sources, gates), encoding="utf-8"
    )
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
