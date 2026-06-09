#!/usr/bin/env python3
"""Sprint 149 ScalingConsistencyForHouLuoConcentration gate emitter.

This deterministic stdlib emitter records the current scaling-consistency
status for the Hou-Luo concentration route.  It is an accounting artifact: it
normalizes the target rows, emits JSON/CSV/Markdown/manifest outputs, and fails
closed if any required row or promotion flag is inconsistent.
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


CONTRACT = "ns_sprint149_scaling_consistency_gate"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint149_scaling_consistency_gate")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"
MANIFEST_NAME = CONTRACT + "_manifest.json"

SPRINT = 149
LANE = 2
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
GATE = "ScalingConsistencyForHouLuoConcentration"
DECISION = "hold_scaling_consistency_unproved_fail_closed"

REQUIRED_ROW_IDS = {
    "beta_positive_scaling_target",
    "corrected_time_available_factor",
    "gronwall_closable_growth_ode",
    "explicit_initial_data_support",
    "source_lower_bound_numerical_support",
    "self_similar_profile_analysis_missing",
    "energy_width_lower_bound_missing",
    "symmetric_hou_luo_bkm_conditional",
    "clay_guard",
}

GLOBAL_FLAGS = {
    "explicit_initial_data_class": True,
    "correct_growth_ode_closable": True,
    "migration_threshold_conditionally_established": True,
    "scaling_consistency_proved": False,
    "beta_positive_scaling_proved": False,
    "symmetric_hou_luo_bkm_finite": False,
    "full_clay_ns_solved": False,
    "clay_navier_stokes_promoted": False,
    "artifact_complete": True,
}

CONTROL_CARD = {
    "O": (
        "Lane 2 owns only scripts/ns_sprint149_scaling_consistency_gate.py "
        "and outputs/ns_sprint149_scaling_consistency_gate/."
    ),
    "R": (
        "Emit a deterministic ScalingConsistencyForHouLuoConcentration gate "
        "with the requested normalized rows and fail-closed proof flags."
    ),
    "C": (
        "A single Python stdlib emitter writes rows JSON, rows CSV, summary "
        "JSON, Markdown, and manifest artifacts through an atomic directory swap."
    ),
    "S": (
        "Explicit initial data, the corrected growth ODE, and a conditional "
        "migration threshold are recorded as support, while beta-positive "
        "scaling and full scaling consistency remain unproved."
    ),
    "L": (
        "Rows are fixed, sorted by gate order, hashed deterministically, and "
        "validated against required IDs plus fail-closed promotion invariants."
    ),
    "P": (
        "Use the artifact as Sprint 149 route-state evidence, not as an Agda "
        "theorem, numerical proof, BKM closure, or Clay promotion."
    ),
    "G": (
        "Validation passes only if all nine rows exist, all requested global "
        "flags match exactly, and Clay/Navier-Stokes promotion flags are false."
    ),
    "F": (
        "Missing: proof of beta-positive concentration scaling, self-similar "
        "profile analysis, energy-width lower bound, and finite symmetric "
        "Hou-Luo BKM closure."
    ),
}


@dataclass(frozen=True)
class GateRow:
    row_id: str
    normalized_name: str
    status: str
    support_level: str
    proved: bool
    conditionally_established: bool
    blocker_or_gap: str
    route_effect: str
    evidence_basis: tuple[str, ...]

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row["sprint"] = SPRINT
        row["lane"] = LANE
        row["contract"] = CONTRACT
        row["program"] = PROGRAM
        row["gate"] = GATE
        row["decision"] = DECISION
        row["evidence_basis"] = list(self.evidence_basis)
        row.update(GLOBAL_FLAGS)
        row["claim_closed"] = self.proved or self.conditionally_established
        row["fail_closed"] = True
        row["no_clay_promotion"] = True
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
    rows = [
        GateRow(
            row_id="beta_positive_scaling_target",
            normalized_name="BetaPositiveScalingTarget",
            status="OPEN_TARGET",
            support_level="target_not_proved",
            proved=False,
            conditionally_established=False,
            blocker_or_gap="positive beta concentration exponent not proved",
            route_effect="keeps_scaling_consistency_gate_open",
            evidence_basis=("Sprint149 scaling gate requirement",),
        ),
        GateRow(
            row_id="corrected_time_available_factor",
            normalized_name="CorrectedTimeAvailableFactor",
            status="RECORDED_SUPPORT",
            support_level="corrected_factor_available",
            proved=True,
            conditionally_established=True,
            blocker_or_gap="does not by itself prove beta-positive scaling",
            route_effect="supports_corrected_scaling_accounting",
            evidence_basis=("corrected Hou-Luo time-available accounting",),
        ),
        GateRow(
            row_id="gronwall_closable_growth_ode",
            normalized_name="GronwallClosableGrowthODE",
            status="RECORDED_SUPPORT",
            support_level="closable_growth_ode_available",
            proved=True,
            conditionally_established=True,
            blocker_or_gap="closable ODE is conditional route support, not BKM closure",
            route_effect="supports_conditional_threshold_bootstrap",
            evidence_basis=("corrected growth ODE ledger",),
        ),
        GateRow(
            row_id="explicit_initial_data_support",
            normalized_name="ExplicitInitialDataSupport",
            status="RECORDED_SUPPORT",
            support_level="explicit_data_class_available",
            proved=True,
            conditionally_established=True,
            blocker_or_gap="initial data class does not force concentration scaling",
            route_effect="anchors_large_data_entry_class",
            evidence_basis=("explicit initial data class packet",),
        ),
        GateRow(
            row_id="source_lower_bound_numerical_support",
            normalized_name="SourceLowerBoundNumericalSupport",
            status="NUMERICAL_SUPPORT_ONLY",
            support_level="numerical_support_available",
            proved=False,
            conditionally_established=True,
            blocker_or_gap="numerical lower support is not a rigorous analytic lower bound",
            route_effect="supports_but_does_not_close_source_lower_bound",
            evidence_basis=("deterministic numerical source lower-bound support",),
        ),
        GateRow(
            row_id="self_similar_profile_analysis_missing",
            normalized_name="SelfSimilarProfileAnalysisMissing",
            status="MISSING_REQUIRED_ANALYSIS",
            support_level="missing",
            proved=False,
            conditionally_established=False,
            blocker_or_gap="self-similar profile analysis has not been supplied",
            route_effect="blocks_scaling_consistency_proof",
            evidence_basis=("Sprint149 missing-analysis inventory",),
        ),
        GateRow(
            row_id="energy_width_lower_bound_missing",
            normalized_name="EnergyWidthLowerBoundMissing",
            status="MISSING_REQUIRED_BOUND",
            support_level="missing",
            proved=False,
            conditionally_established=False,
            blocker_or_gap="energy-width lower bound has not been supplied",
            route_effect="blocks_beta_positive_scaling_proof",
            evidence_basis=("Sprint149 missing-bound inventory",),
        ),
        GateRow(
            row_id="symmetric_hou_luo_bkm_conditional",
            normalized_name="SymmetricHouLuoBKMConditional",
            status="CONDITIONAL_NOT_FINITE",
            support_level="conditional_bkm_route",
            proved=False,
            conditionally_established=True,
            blocker_or_gap="symmetric Hou-Luo BKM finiteness is not established",
            route_effect="prevents_bkm_or_clay_promotion",
            evidence_basis=("conditional symmetric Hou-Luo BKM ledger",),
        ),
        GateRow(
            row_id="clay_guard",
            normalized_name="ClayGuard",
            status="FAIL_CLOSED_NOT_PROMOTED",
            support_level="guard",
            proved=False,
            conditionally_established=False,
            blocker_or_gap="full Clay Navier-Stokes is not solved or promoted",
            route_effect="blocks_any_clay_promotion",
            evidence_basis=("Sprint149 fail-closed promotion guard",),
        ),
    ]
    return [row.as_row() for row in rows]


def validate(rows: list[dict[str, Any]], summary: dict[str, Any] | None = None) -> list[str]:
    failures: list[str] = []
    by_id = {str(row["row_id"]): row for row in rows}
    missing = sorted(REQUIRED_ROW_IDS.difference(by_id))
    extra = sorted(set(by_id).difference(REQUIRED_ROW_IDS))
    if missing:
        failures.append("missing required row ids: " + ", ".join(missing))
    if extra:
        failures.append("unexpected row ids: " + ", ".join(extra))

    expected_status = {
        "beta_positive_scaling_target": "OPEN_TARGET",
        "corrected_time_available_factor": "RECORDED_SUPPORT",
        "gronwall_closable_growth_ode": "RECORDED_SUPPORT",
        "explicit_initial_data_support": "RECORDED_SUPPORT",
        "source_lower_bound_numerical_support": "NUMERICAL_SUPPORT_ONLY",
        "self_similar_profile_analysis_missing": "MISSING_REQUIRED_ANALYSIS",
        "energy_width_lower_bound_missing": "MISSING_REQUIRED_BOUND",
        "symmetric_hou_luo_bkm_conditional": "CONDITIONAL_NOT_FINITE",
        "clay_guard": "FAIL_CLOSED_NOT_PROMOTED",
    }
    for row_id, status in expected_status.items():
        row = by_id.get(row_id)
        if row is not None and row["status"] != status:
            failures.append(f"{row_id} status is {row['status']!r}, expected {status!r}")

    for key, expected in GLOBAL_FLAGS.items():
        if any(row.get(key) is not expected for row in rows):
            failures.append(f"row flag {key} does not match expected {expected!r}")
        if summary is not None and summary.get(key) is not expected:
            failures.append(f"summary flag {key} does not match expected {expected!r}")

    if any(row["row_id"] == "clay_guard" and row["proved"] for row in rows):
        failures.append("clay_guard cannot be proved")
    if summary is not None and summary.get("promotion_allowed") is not False:
        failures.append("summary promotion_allowed must be false")
    return failures


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    status_counts: dict[str, int] = {}
    support_counts: dict[str, int] = {}
    for row in rows:
        status_counts[str(row["status"])] = status_counts.get(str(row["status"]), 0) + 1
        support = str(row["support_level"])
        support_counts[support] = support_counts.get(support, 0) + 1

    row_ids = [str(row["row_id"]) for row in rows]
    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "program": PROGRAM,
        "gate": GATE,
        "decision": DECISION,
        "row_count": len(rows),
        "required_row_ids": sorted(REQUIRED_ROW_IDS),
        "observed_row_ids": row_ids,
        "missing_required_row_ids": sorted(REQUIRED_ROW_IDS.difference(row_ids)),
        "extra_row_ids": sorted(set(row_ids).difference(REQUIRED_ROW_IDS)),
        "status_counts": status_counts,
        "support_counts": support_counts,
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
        {k: v for k, v in summary.items() if k != "summary_hash"}
    )
    return summary


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = list(rows[0].keys())
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow(
                {
                    key: json.dumps(value, sort_keys=True) if isinstance(value, list) else value
                    for key, value in row.items()
                }
            )


def render_markdown(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# Sprint 149 Scaling Consistency Gate",
        "",
        "## Decision",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Gate: `{summary['gate']}`",
        f"- Decision: `{summary['decision']}`",
        f"- Row count: `{summary['row_count']}`",
        f"- Scaling consistency proved: `{summary['scaling_consistency_proved']}`",
        f"- Beta-positive scaling proved: `{summary['beta_positive_scaling_proved']}`",
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
            "## Normalized Rows",
            "",
            "| row_id | status | support_level | proved | conditionally_established | route_effect |",
            "| --- | --- | --- | --- | --- | --- |",
        ]
    )
    for row in rows:
        lines.append(
            "| {row_id} | {status} | {support_level} | {proved} | "
            "{conditionally_established} | {route_effect} |".format(**row)
        )
    lines.extend(
        [
            "",
            "## Guard",
            "",
            (
                "This artifact records conditional support only. It does not prove "
                "ScalingConsistencyForHouLuoConcentration, beta-positive scaling, "
                "finite symmetric Hou-Luo BKM closure, or full Clay Navier-Stokes."
            ),
            "",
        ]
    )
    return "\n".join(lines)


def build_manifest(
    repo_root: Path, out_dir: Path, rows: list[dict[str, Any]], summary: dict[str, Any]
) -> dict[str, Any]:
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
        {k: v for k, v in manifest.items() if k != "manifest_hash"}
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
                "scaling_consistency_proved": summary["scaling_consistency_proved"],
                "beta_positive_scaling_proved": summary["beta_positive_scaling_proved"],
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
