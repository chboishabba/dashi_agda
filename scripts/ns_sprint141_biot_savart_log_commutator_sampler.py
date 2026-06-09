#!/usr/bin/env python3
"""Sprint 141 Biot-Savart log commutator sampler.

This deterministic sampler records a local ledger for the log amplification
hazard in partial_z u^r when source rings or off-axis annuli are nearly
coincident.  It is a diagnostic artifact only: bounded local rows and hazard
rows are both emitted, and the conclusion is fail-closed.  No global
Navier-Stokes proof, no log-aware commutator domination theorem, and no Clay
promotion are produced.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint141_biot_savart_log_commutator_sampler"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint141_biot_savart_log_commutator_sampler")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"

SPRINT = 141
LANE = 3
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
GATE = "TransportCommutatorDomination"
BLOCKER = "BiotSavartLogLossInPartialZUr"

REFERENCE_RADIUS = 1.0
LOCAL_LOG_BUDGET = 4.0
DOMINATION_BUDGET = 1.0
EPSILON = 1.0e-15


@dataclass(frozen=True)
class SampleCase:
    case_id: str
    geometry: str
    source_model: str
    target_radius: float
    source_radius: float
    axial_gap: float
    radial_gap: float
    source_weight: float
    partial_r_u1_scale: float
    benign_baseline: float
    note: str


@dataclass(frozen=True)
class LedgerRow:
    row_id: str
    case_id: str
    geometry: str
    source_model: str
    target_radius: float
    source_radius: float
    axial_gap: float
    radial_gap: float
    separation: float
    log_amplification: float
    annular_alignment: float
    source_weight: float
    partial_z_ur_proxy: float
    partial_r_u1_scale: float
    commutator_positive_part_proxy: float
    benign_baseline: float
    amplification_over_baseline: float
    local_bounded_row: bool
    log_loss_hazard_row: bool
    domination_budget: float
    domination_margin_proxy: float
    log_aware_commutator_domination_proved: bool
    global_proof_claimed: bool
    clay_navier_stokes_promoted: bool
    promotion_allowed: bool
    classification: str
    note: str

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row["blocker"] = BLOCKER
        row["gate"] = GATE
        row["program"] = PROGRAM
        row["sprint"] = SPRINT
        row["lane"] = LANE
        row["row_hash"] = stable_hash({k: v for k, v in row.items() if k != "row_hash"})
        return row


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def stable_hash(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def clean(value: float) -> float:
    if abs(value) < 1.0e-14:
        return 0.0
    return float(f"{value:.15g}")


def sample_cases() -> tuple[SampleCase, ...]:
    return (
        SampleCase(
            case_id="local_ring_separated_moderate",
            geometry="coaxial_ring_pair",
            source_model="same-sign smooth vorticity ring, separated axial supports",
            target_radius=1.0,
            source_radius=1.03,
            axial_gap=0.28,
            radial_gap=0.03,
            source_weight=0.18,
            partial_r_u1_scale=0.55,
            benign_baseline=0.72,
            note="Separated supports keep the logarithmic kernel ledger local.",
        ),
        SampleCase(
            case_id="off_axis_annulus_local",
            geometry="off_axis_annulus",
            source_model="annular patch with radial offset away from target ring",
            target_radius=1.0,
            source_radius=1.18,
            axial_gap=0.16,
            radial_gap=0.18,
            source_weight=0.14,
            partial_r_u1_scale=0.48,
            benign_baseline=0.69,
            note="Radial offset limits near-coincident alignment despite annular geometry.",
        ),
        SampleCase(
            case_id="near_coincident_ring_log_loss",
            geometry="nearly_coincident_coaxial_rings",
            source_model="thin ring pair with small axial gap and matched radius",
            target_radius=1.0,
            source_radius=1.001,
            axial_gap=0.004,
            radial_gap=0.001,
            source_weight=0.22,
            partial_r_u1_scale=0.72,
            benign_baseline=0.74,
            note="Nearly coincident rings expose a logarithmic amplification not absorbed by the local ledger.",
        ),
        SampleCase(
            case_id="off_axis_annulus_grazing_log_loss",
            geometry="grazing_off_axis_annuli",
            source_model="two annuli with small radial and axial mismatch",
            target_radius=1.0,
            source_radius=1.012,
            axial_gap=0.009,
            radial_gap=0.012,
            source_weight=0.2,
            partial_r_u1_scale=0.8,
            benign_baseline=0.76,
            note="Off-axis annular grazing keeps a live log-loss hazard.",
        ),
        SampleCase(
            case_id="multi_scale_annulus_unresolved",
            geometry="nested_off_axis_annuli",
            source_model="nested annular shells with one unresolved near-coincident scale",
            target_radius=1.0,
            source_radius=0.997,
            axial_gap=0.0015,
            radial_gap=0.003,
            source_weight=0.17,
            partial_r_u1_scale=0.92,
            benign_baseline=0.7,
            note="A small nested scale can dominate the otherwise bounded annular contribution.",
        ),
    )


def build_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for index, case in enumerate(sample_cases()):
        separation = math.hypot(case.axial_gap, case.radial_gap)
        log_amplification = math.log1p(REFERENCE_RADIUS / max(separation, EPSILON))
        annular_alignment = 1.0 / (1.0 + abs(case.source_radius - case.target_radius))
        partial_z_ur_proxy = case.source_weight * annular_alignment * log_amplification
        commutator_proxy = max(0.0, partial_z_ur_proxy * case.partial_r_u1_scale)
        amplification_ratio = commutator_proxy / case.benign_baseline
        hazard = (
            log_amplification > LOCAL_LOG_BUDGET
            or amplification_ratio > DOMINATION_BUDGET
        )
        local = not hazard
        classification = (
            "local_bounded_log_row"
            if local
            else "log_loss_hazard_commutator_domination_unproved"
        )
        row = LedgerRow(
            row_id=f"r{index:03d}",
            case_id=case.case_id,
            geometry=case.geometry,
            source_model=case.source_model,
            target_radius=case.target_radius,
            source_radius=case.source_radius,
            axial_gap=case.axial_gap,
            radial_gap=case.radial_gap,
            separation=clean(separation),
            log_amplification=clean(log_amplification),
            annular_alignment=clean(annular_alignment),
            source_weight=case.source_weight,
            partial_z_ur_proxy=clean(partial_z_ur_proxy),
            partial_r_u1_scale=case.partial_r_u1_scale,
            commutator_positive_part_proxy=clean(commutator_proxy),
            benign_baseline=case.benign_baseline,
            amplification_over_baseline=clean(amplification_ratio),
            local_bounded_row=local,
            log_loss_hazard_row=hazard,
            domination_budget=DOMINATION_BUDGET,
            domination_margin_proxy=clean(DOMINATION_BUDGET - amplification_ratio),
            log_aware_commutator_domination_proved=False,
            global_proof_claimed=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
            classification=classification,
            note=case.note,
        ).as_row()
        row["hazard_id"] = case.case_id if hazard else ""
        row["hazard_name"] = (
            "log_loss_hazard" if hazard else "local_bounded_reference_row"
        )
        row["constants_absent"] = True
        row["constant_compatibility_absent"] = True
        row["log_aware_theorem_absent"] = True
        row["log_aware_commutator_theorem_absent"] = True
        row["missing_log_aware_theorem"] = (
            "LogAwareCommutatorDominationForVBarrier"
        )
        row["claim_closed"] = False
        row["claim_proved"] = False
        row["claim_proven"] = False
        rows.append(row)
    return rows


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    local_rows = [row for row in rows if row["local_bounded_row"]]
    hazard_rows = [row for row in rows if row["log_loss_hazard_row"]]
    max_log = max(float(row["log_amplification"]) for row in rows)
    max_ratio = max(float(row["amplification_over_baseline"]) for row in rows)
    return {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "program": PROGRAM,
        "gate": GATE,
        "blocker": BLOCKER,
        "row_count": len(rows),
        "local_bounded_row_count": len(local_rows),
        "log_loss_hazard_row_count": len(hazard_rows),
        "local_log_budget": LOCAL_LOG_BUDGET,
        "domination_budget": DOMINATION_BUDGET,
        "max_log_amplification": clean(max_log),
        "max_amplification_over_baseline": clean(max_ratio),
        "has_local_bounded_rows": bool(local_rows),
        "has_log_loss_hazard_rows": bool(hazard_rows),
        "near_coincident_ring_or_annulus_hazard_observed": bool(hazard_rows),
        "log_aware_commutator_domination_proved": False,
        "transport_commutator_domination_closed": False,
        "commutator_domination_closed": False,
        "domination_closed": False,
        "claim_closed": False,
        "global_proof": False,
        "global_proof_closed": False,
        "global_navier_stokes_proof_claimed": False,
        "full_clay_ns_solved": False,
        "full_clay_navier_stokes_solved": False,
        "clay_navier_stokes_promoted": False,
        "promotion_allowed": False,
        "constants_absent": True,
        "constant_compatibility_absent": True,
        "log_aware_theorem_absent": True,
        "log_aware_commutator_theorem_absent": True,
        "missing_log_aware_theorem": "LogAwareCommutatorDominationForVBarrier",
        "route_decision": "fail_closed_log_loss_hazard_open",
        "conclusion": (
            "Local bounded rows coexist with near-coincident ring/off-axis annulus "
            "log-loss hazard rows; log-aware commutator domination is not proved."
        ),
        "complete": True,
        "exit_code": 0,
    }


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        raise ValueError("cannot write empty row set")
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def format_value(value: Any) -> str:
    if isinstance(value, bool):
        return str(value).lower()
    if isinstance(value, float):
        return f"{value:.12g}"
    return str(value)


def markdown_table(rows: list[dict[str, Any]]) -> str:
    headers = (
        "row",
        "case",
        "geometry",
        "sep",
        "log amp",
        "comm proxy",
        "ratio",
        "local",
        "hazard",
        "class",
    )
    keys = (
        "row_id",
        "case_id",
        "geometry",
        "separation",
        "log_amplification",
        "commutator_positive_part_proxy",
        "amplification_over_baseline",
        "local_bounded_row",
        "log_loss_hazard_row",
        "classification",
    )
    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    for row in rows:
        lines.append("| " + " | ".join(format_value(row[key]) for key in keys) + " |")
    return "\n".join(lines)


def build_report(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    return "\n".join(
        [
            "# Sprint 141 Biot-Savart Log Commutator Sampler",
            "",
            "## Decision",
            "",
            summary["conclusion"],
            "",
            "- Route decision: `fail_closed_log_loss_hazard_open`",
            "- Log-aware commutator domination proved: `false`",
            "- Global Navier-Stokes proof claimed: `false`",
            "- Clay promotion allowed: `false`",
            "",
            "## Ledger",
            "",
            markdown_table(rows),
            "",
            "## Validation",
            "",
            "The artifact contains both local bounded rows and log-loss hazard rows. "
            "Every row and the summary keep global proof, route closure, and promotion flags false.",
            "",
        ]
    )


def validate(rows: list[dict[str, Any]], summary: dict[str, Any]) -> None:
    if not rows:
        raise ValueError("sampler emitted no rows")
    if not any(row["local_bounded_row"] for row in rows):
        raise ValueError("expected at least one local bounded row")
    if not any(row["log_loss_hazard_row"] for row in rows):
        raise ValueError("expected at least one log-loss hazard row")
    forbidden_row_flags = (
        "log_aware_commutator_domination_proved",
        "global_proof_claimed",
        "clay_navier_stokes_promoted",
        "promotion_allowed",
    )
    for row in rows:
        for flag in forbidden_row_flags:
            if row[flag]:
                raise ValueError(f"row {row['row_id']} illegally set {flag}=true")
    forbidden_summary_flags = (
        "log_aware_commutator_domination_proved",
        "transport_commutator_domination_closed",
        "global_navier_stokes_proof_claimed",
        "full_clay_navier_stokes_solved",
        "clay_navier_stokes_promoted",
        "promotion_allowed",
    )
    for flag in forbidden_summary_flags:
        if summary[flag]:
            raise ValueError(f"summary illegally set {flag}=true")
    if summary["route_decision"] != "fail_closed_log_loss_hazard_open":
        raise ValueError("route decision must remain fail-closed")


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = repo_root / out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    rows = build_rows()
    summary = build_summary(rows)
    validate(rows, summary)

    write_json(out_dir / ROWS_JSON_NAME, rows)
    write_json(out_dir / SUMMARY_NAME, summary)
    write_csv(out_dir / ROWS_CSV_NAME, rows)
    (out_dir / REPORT_NAME).write_text(build_report(summary, rows), encoding="utf-8")

    print(json.dumps(summary, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
