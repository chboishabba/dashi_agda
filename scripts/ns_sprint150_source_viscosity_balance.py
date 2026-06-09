#!/usr/bin/env python3
"""Sprint 150 source-integral / retained-viscosity balance emitter.

This deterministic stdlib ledger sharpens the Hou-Luo concentration gap after
Sprint 149.  It decomposes the source integral and retained viscosity budgets,
records the available adverse inequality directions, and fails closed unless
all promotion flags remain false.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import shutil
import sys
import tempfile
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint150_source_viscosity_balance"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint150_source_viscosity_balance")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"
MANIFEST_NAME = CONTRACT + "_manifest.json"

SPRINT = 150
LANE = 1
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
GATE = "LocalizedSourceViscosityBalanceAtMigratingMaximum"
PARENT_GATE = "ScalingConsistencyForHouLuoConcentration"
DECISION = "hold_source_viscosity_balance_unproved_fail_closed"

REQUIRED_ROW_IDS = {
    "source_integral_lower_bound",
    "retained_viscosity_lower_bound",
    "off_axis_gain_absorption",
    "log_feedback_absorption",
    "cutoff_localization_error",
    "boundary_annular_budget",
    "nonlocal_tail_control",
    "large_data_uniformity",
    "localized_source_beats_viscosity",
    "clay_guard",
}

GLOBAL_FLAGS = {
    "source_integral_lower_bound_proved": False,
    "retained_viscosity_lower_bound_proved": False,
    "source_beats_retained_viscosity": False,
    "localized_source_viscosity_balance_proved": False,
    "migration_initiation_threshold_promoted": False,
    "scaling_consistency_promoted": False,
    "symmetric_hou_luo_bkm_finite": False,
    "full_clay_ns_solved": False,
    "clay_navier_stokes_promoted": False,
    "artifact_complete": True,
}

CONTROL_CARD = {
    "O": "Lane 1 owns only the Sprint150 source/viscosity ledger and artifacts.",
    "R": (
        "Decompose the source-integral and retained-viscosity estimates needed "
        "before migration threshold, scaling consistency, BKM, or Clay promotion."
    ),
    "C": (
        "A stdlib Python emitter writes rows JSON, rows CSV, summary JSON, "
        "Markdown, and manifest through an atomic directory swap."
    ),
    "S": (
        "The available normalized directions are adverse: source observed 82 "
        "is below required 100, retained viscosity observed 46 is below "
        "required 100, and off-axis/log demands exceed baseline."
    ),
    "L": (
        "Rows < analytic lemmas < localized balance < migration threshold < "
        "scaling consistency < symmetric BKM < Clay."
    ),
    "P": (
        "Calculate source lower bound and retained-viscosity lower bound first; "
        "then discharge off-axis, log, cutoff, boundary, nonlocal, and uniformity gaps."
    ),
    "G": (
        "Validation requires ten rows, explicit blockers, exact false promotion "
        "flags, and no theorem/proof/Clay closure."
    ),
    "F": (
        "Nine analytic lemmas remain missing; the artifact is a gap reducer, not "
        "a Navier-Stokes proof."
    ),
}


@dataclass(frozen=True)
class BalanceCase:
    row_id: str
    component_family: str
    normalized_quantity: str
    observed_value: float
    required_value: float
    status: str
    support_level: str
    analytic_lemma_required: str
    blocker: str
    route_effect: str

    def as_row(self) -> dict[str, Any]:
        margin = clean(self.observed_value - self.required_value)
        ratio = None if self.required_value == 0 else clean(self.observed_value / self.required_value)
        row: dict[str, Any] = asdict(self)
        row.update(
            {
                "sprint": SPRINT,
                "lane": LANE,
                "contract": CONTRACT,
                "program": PROGRAM,
                "gate": GATE,
                "parent_gate": PARENT_GATE,
                "decision": DECISION,
                "margin_to_required": margin,
                "ratio_to_required": ratio,
                "claim_closed": False,
                "claim_proved": False,
                "claim_proven": False,
                "promotion_allowed": False,
                "fail_closed": True,
                "no_clay_promotion": True,
            }
        )
        row.update(GLOBAL_FLAGS)
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


def file_sha256(path: Path) -> str | None:
    if not path.exists():
        return None
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def display_path(path: Path, repo_root: Path) -> str:
    try:
        return str(path.relative_to(repo_root))
    except ValueError:
        return str(path)


def build_rows() -> list[dict[str, Any]]:
    cases = [
        BalanceCase(
            "source_integral_lower_bound",
            "source",
            "localized integral of 2*u1*partial_z_u1 at migrating maximum",
            82.0,
            100.0,
            "OBSERVED_BELOW_REQUIRED",
            "numerical_support_only",
            "SourceIntegralLowerBoundForMigratingMaximum",
            "analytic lower bound missing",
            "blocks migration initiation threshold",
        ),
        BalanceCase(
            "retained_viscosity_lower_bound",
            "viscosity",
            "retained localized viscous damping at migrating maximum",
            46.0,
            100.0,
            "RETAINED_VISCOSITY_DEFICIT",
            "baseline_deficit_recorded",
            "RetainedViscosityLowerBoundAtMigratingMaximum",
            "uniform retained viscosity lower bound missing",
            "blocks source versus viscosity comparison",
        ),
        BalanceCase(
            "off_axis_gain_absorption",
            "gain",
            "off-axis amplification demand against unit baseline",
            134.0,
            100.0,
            "ADVERSE_GAIN_ABOVE_BASELINE",
            "adverse_direction_recorded",
            "OffAxisGainAbsorptionLemma",
            "off-axis gain absorption missing",
            "prevents localized balance closure",
        ),
        BalanceCase(
            "log_feedback_absorption",
            "feedback",
            "log-supercritical feedback demand against unit baseline",
            172.0,
            100.0,
            "ADVERSE_LOG_ABOVE_BASELINE",
            "adverse_direction_recorded",
            "LogFeedbackAbsorptionLemma",
            "log feedback absorption missing",
            "prevents Gronwall closure from becoming unconditional",
        ),
        BalanceCase(
            "cutoff_localization_error",
            "localization",
            "cutoff commutator and transport error budget",
            0.0,
            1.0,
            "LEMMA_MISSING",
            "named_obligation",
            "CutoffLocalizationErrorLemma",
            "cutoff transport/localization estimate missing",
            "blocks passage from model integral to localized identity",
        ),
        BalanceCase(
            "boundary_annular_budget",
            "boundary",
            "annular flux and boundary-image correction budget",
            0.0,
            1.0,
            "LEMMA_MISSING",
            "named_obligation",
            "BoundaryImageCorrectionLemma",
            "annular and boundary-image bounds missing",
            "blocks Hou-Luo wall geometry uniformity",
        ),
        BalanceCase(
            "nonlocal_tail_control",
            "nonlocal",
            "Biot-Savart nonlocal tail controlled below source margin",
            0.0,
            1.0,
            "LEMMA_MISSING",
            "named_obligation",
            "NonlocalTailSmallnessLemma",
            "nonlocal tail smallness missing",
            "blocks source lower-bound localization",
        ),
        BalanceCase(
            "large_data_uniformity",
            "uniformity",
            "constant package uniform over smooth large-data family",
            0.0,
            1.0,
            "LEMMA_MISSING",
            "named_obligation",
            "LargeDataUniformityOfConstantsLemma",
            "large-data uniformity missing",
            "prevents threshold from being data-class theorem",
        ),
        BalanceCase(
            "localized_source_beats_viscosity",
            "comparison",
            "source lower bound exceeds retained viscosity plus losses",
            0.0,
            1.0,
            "COMPARISON_NOT_PROVED",
            "target_comparison",
            "LocalizedSourceBeatsRetainedViscosityLemma",
            "source-beats-viscosity inequality missing",
            "keeps localized balance false/open",
        ),
        BalanceCase(
            "clay_guard",
            "governance",
            "Clay promotion requires all previous gates plus mechanism exhaustion",
            0.0,
            1.0,
            "FAIL_CLOSED_NOT_PROMOTED",
            "guard",
            "MechanismExhaustionForFullClay",
            "mechanism exhaustion and standard Clay translation missing",
            "blocks all NS Clay promotion",
        ),
    ]
    return [case.as_row() for case in cases]


def validate(rows: list[dict[str, Any]], summary: dict[str, Any] | None = None) -> list[str]:
    failures: list[str] = []
    ids = {str(row["row_id"]) for row in rows}
    missing = sorted(REQUIRED_ROW_IDS - ids)
    extra = sorted(ids - REQUIRED_ROW_IDS)
    if missing:
        failures.append("missing rows: " + ", ".join(missing))
    if extra:
        failures.append("unexpected rows: " + ", ".join(extra))
    for row in rows:
        if not row.get("blocker"):
            failures.append(f"{row['row_id']} blocker missing")
        if row.get("claim_closed") or row.get("claim_proved") or row.get("claim_proven"):
            failures.append(f"{row['row_id']} incorrectly closes a claim")
        if row.get("promotion_allowed") or row.get("clay_navier_stokes_promoted"):
            failures.append(f"{row['row_id']} incorrectly allows promotion")
        for key, expected in GLOBAL_FLAGS.items():
            if row.get(key) is not expected:
                failures.append(f"{row['row_id']} flag {key} expected {expected}")
    if summary is not None:
        for key, expected in GLOBAL_FLAGS.items():
            if summary.get(key) is not expected:
                failures.append(f"summary flag {key} expected {expected}")
        if summary.get("promotion_allowed") is not False:
            failures.append("summary promotion_allowed must be false")
    return failures


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    status_counts: dict[str, int] = {}
    family_counts: dict[str, int] = {}
    for row in rows:
        status = str(row["status"])
        family = str(row["component_family"])
        status_counts[status] = status_counts.get(status, 0) + 1
        family_counts[family] = family_counts.get(family, 0) + 1
    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "program": PROGRAM,
        "gate": GATE,
        "parent_gate": PARENT_GATE,
        "decision": DECISION,
        "row_count": len(rows),
        "required_row_ids": sorted(REQUIRED_ROW_IDS),
        "observed_row_ids": [str(row["row_id"]) for row in rows],
        "status_counts": status_counts,
        "family_counts": family_counts,
        "source_observed": 82,
        "source_required": 100,
        "source_deficit": 18,
        "retained_viscosity_observed": 46,
        "retained_viscosity_required": 100,
        "retained_viscosity_deficit": 54,
        "analytic_lemma_count": 9,
        "promotion_allowed": False,
        "fail_closed": True,
        "control_card": CONTROL_CARD,
        "invariant_checked": False,
        "invariant_valid": False,
        "invariant_failures": [],
    }
    summary.update(GLOBAL_FLAGS)
    failures = validate(rows, summary)
    summary["invariant_failures"] = failures
    summary["invariant_checked"] = True
    summary["invariant_valid"] = not failures
    summary["artifact_complete"] = not failures and GLOBAL_FLAGS["artifact_complete"]
    summary["summary_hash"] = stable_hash(
        {key: value for key, value in summary.items() if key != "summary_hash"}
    )
    return summary


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def render_markdown(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# Sprint 150 Source/Viscosity Balance",
        "",
        f"- Gate: `{summary['gate']}`",
        f"- Decision: `{summary['decision']}`",
        f"- Row count: `{summary['row_count']}`",
        f"- Source observed/required: `{summary['source_observed']}/{summary['source_required']}`",
        (
            "- Retained viscosity observed/required: "
            f"`{summary['retained_viscosity_observed']}/{summary['retained_viscosity_required']}`"
        ),
        f"- Clay promoted: `{summary['clay_navier_stokes_promoted']}`",
        "",
        "## O/R/C/S/L/P/G/F",
        "",
    ]
    for key in ("O", "R", "C", "S", "L", "P", "G", "F"):
        lines.append(f"- {key}: {CONTROL_CARD[key]}")
    lines.extend(
        [
            "",
            "## Rows",
            "",
            "| row_id | family | status | observed | required | lemma | blocker |",
            "| --- | --- | --- | ---: | ---: | --- | --- |",
        ]
    )
    for row in rows:
        lines.append(
            "| {row_id} | {component_family} | {status} | {observed_value:.6g} | "
            "{required_value:.6g} | {analytic_lemma_required} | {blocker} |".format(**row)
        )
    lines.extend(
        [
            "",
            "## Guard",
            "",
            (
                "This ledger names the analytic support obligations. It does not "
                "prove the localized balance, BKM finiteness, or Clay Navier-Stokes."
            ),
            "",
        ]
    )
    return "\n".join(lines)


def build_manifest(repo_root: Path, out_dir: Path, rows: list[dict[str, Any]], summary: dict[str, Any]) -> dict[str, Any]:
    files = [
        out_dir / ROWS_JSON_NAME,
        out_dir / ROWS_CSV_NAME,
        out_dir / SUMMARY_NAME,
        out_dir / REPORT_NAME,
    ]
    manifest: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "gate": GATE,
        "decision": DECISION,
        "row_count": len(rows),
        "artifact_complete": summary["artifact_complete"],
        "invariant_valid": summary["invariant_valid"],
        "control_card": CONTROL_CARD,
        "files": [
            {
                "path": display_path(path, repo_root),
                "exists": path.exists(),
                "sha256": file_sha256(path),
            }
            for path in files
        ],
    }
    manifest.update(GLOBAL_FLAGS)
    manifest["manifest_hash"] = stable_hash(
        {key: value for key, value in manifest.items() if key != "manifest_hash"}
    )
    return manifest


def write_outputs(repo_root: Path, out_dir: Path, rows: list[dict[str, Any]], summary: dict[str, Any]) -> None:
    final_out = out_dir if out_dir.is_absolute() else repo_root / out_dir
    final_out.parent.mkdir(parents=True, exist_ok=True)
    temp_dir = Path(tempfile.mkdtemp(prefix=f".{CONTRACT}.", dir=final_out.parent))
    try:
        write_json(temp_dir / ROWS_JSON_NAME, rows)
        write_csv(temp_dir / ROWS_CSV_NAME, rows)
        write_json(temp_dir / SUMMARY_NAME, summary)
        (temp_dir / REPORT_NAME).write_text(render_markdown(summary, rows), encoding="utf-8")
        manifest = build_manifest(repo_root, temp_dir, rows, summary)
        write_json(temp_dir / MANIFEST_NAME, manifest)
        if final_out.exists():
            shutil.rmtree(final_out)
        os.replace(temp_dir, final_out)
        manifest = build_manifest(repo_root, final_out, rows, summary)
        write_json(final_out / MANIFEST_NAME, manifest)
    except Exception:
        shutil.rmtree(temp_dir, ignore_errors=True)
        raise


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    rows = build_rows()
    summary = build_summary(rows)
    write_outputs(repo_root, args.out_dir, rows, summary)
    print(
        json.dumps(
            {
                "contract": CONTRACT,
                "artifact_complete": summary["artifact_complete"],
                "invariant_valid": summary["invariant_valid"],
                "row_count": summary["row_count"],
                "source_integral_lower_bound_proved": summary[
                    "source_integral_lower_bound_proved"
                ],
                "localized_source_viscosity_balance_proved": summary[
                    "localized_source_viscosity_balance_proved"
                ],
                "clay_navier_stokes_promoted": summary["clay_navier_stokes_promoted"],
                "out_dir": display_path(
                    args.out_dir if args.out_dir.is_absolute() else repo_root / args.out_dir,
                    repo_root,
                ),
            },
            sort_keys=True,
        )
    )
    return 0 if summary["invariant_valid"] else 1


if __name__ == "__main__":
    sys.exit(main())
