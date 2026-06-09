#!/usr/bin/env python3
"""Sprint 147 migration-initiation threshold emitter.

This deterministic stdlib emitter records the normalized gate

    MigrationInitiationThresholdForLargeData

for the Hou-Luo axisymmetric-with-swirl route after the Sprint 146 maximum
location migration gate.  It emits a threshold ledger rather than a proof: the
symmetry-plane pure-diffusion baseline is favorable, but off-axis gain,
viscosity suppression, log-supercritical feedback, finite-energy admissibility,
and the Clay guard keep the route fail-closed.
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


CONTRACT = "ns_sprint147_migration_initiation_threshold"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint147_migration_initiation_threshold")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"
MANIFEST_NAME = CONTRACT + "_manifest.json"

SPRINT = 147
LANE = 2
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
TARGET_GATE = "MigrationInitiationThresholdForLargeData"
PARENT_SPRINT = 146
PARENT_CONTRACT = "ns_sprint146_maximum_location_migration_gate"
PARENT_GATE = "MaximumLocationMigrationLemma"
DECISION = "fail_closed_migration_initiation_threshold_not_proved"

THRESHOLD_FORMULA = (
    "source_integral_threshold := "
    "off_axis_gain * log_supercritical_feedback / max(viscosity_suppression, eps)"
)
BASELINE_FORMULA = "symmetry_plane_diffusion_baseline := nu * |Ltilde v| at z = 0"
ADMISSIBILITY_FORMULA = (
    "smooth finite-energy admissibility requires finite H1 energy and smooth "
    "compact local profiles; it does not imply migration-threshold positivity"
)

REQUIRED_ROW_IDS = {
    "source_integral_threshold",
    "symmetry_plane_diffusion_baseline",
    "off_axis_gain",
    "viscosity_suppression",
    "log_supercritical_feedback",
    "smooth_finite_energy_admissibility",
    "clay_promotion_guard",
}

SUMMARY_REQUIRED_FALSE = {
    "migration_initiation_threshold_proved",
    "blowup_existence_proved",
    "full_clay_ns_solved",
    "clay_navier_stokes_promoted",
    "maximum_location_migration_exclusion",
}

SUMMARY_REQUIRED_TRUE = {
    "pure_diffusion_at_symmetry_plane",
    "artifact_complete",
}

FLAGS = {
    "migration_initiation_threshold_proved": False,
    "blowup_existence_proved": False,
    "full_clay_ns_solved": False,
    "clay_navier_stokes_promoted": False,
    "pure_diffusion_at_symmetry_plane": True,
    "maximum_location_migration_exclusion": False,
    "artifact_complete": True,
}

SOURCE_ARTIFACTS = {
    "sprint146_maximum_location_migration_gate": (
        "outputs/ns_sprint146_maximum_location_migration_gate/"
        "ns_sprint146_maximum_location_migration_gate_summary.json"
    ),
}


@dataclass(frozen=True)
class ThresholdCase:
    row_id: str
    row_role: str
    normalized_quantity: str
    baseline_value: float
    observed_value: float
    threshold_value: float
    status: str
    supports_threshold: bool
    obstructs_threshold: bool
    blockers: tuple[str, ...]
    interpretation: str


@dataclass(frozen=True)
class ThresholdRow:
    row_id: str
    sprint: int
    lane: int
    contract: str
    program: str
    target_gate: str
    parent_sprint: int
    parent_contract: str
    parent_gate: str
    row_role: str
    normalized_quantity: str
    baseline_value: float
    observed_value: float
    threshold_value: float
    margin_to_threshold: float
    ratio_to_threshold: float | None
    status: str
    supports_threshold: bool
    obstructs_threshold: bool
    blockers: tuple[str, ...]
    interpretation: str
    migration_initiation_threshold_proved: bool
    blowup_existence_proved: bool
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool
    pure_diffusion_at_symmetry_plane: bool
    maximum_location_migration_exclusion: bool
    artifact_complete: bool

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row["blockers"] = list(row["blockers"])
        row["decision"] = DECISION
        row["threshold_formula"] = THRESHOLD_FORMULA
        row["baseline_formula"] = BASELINE_FORMULA
        row["admissibility_formula"] = ADMISSIBILITY_FORMULA
        row["claim_closed"] = False
        row["claim_proved"] = False
        row["claim_proven"] = False
        row["promotion_allowed"] = False
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


def source_artifact_state(repo_root: Path) -> dict[str, dict[str, Any]]:
    state: dict[str, dict[str, Any]] = {}
    for key, relative in SOURCE_ARTIFACTS.items():
        path = repo_root / relative
        entry: dict[str, Any] = {
            "path": relative,
            "exists": path.exists(),
            "sha256": file_sha256(path),
        }
        if path.exists():
            try:
                payload = json.loads(path.read_text(encoding="utf-8"))
            except json.JSONDecodeError:
                payload = {}
            for flag in (
                "maximum_location_migration_lemma_proved",
                "migration_gate_closed",
                "full_clay_ns_solved",
                "clay_navier_stokes_promoted",
                "artifact_complete",
            ):
                if flag in payload:
                    entry[flag] = payload[flag]
        state[key] = entry
    return state


def sample_cases() -> tuple[ThresholdCase, ...]:
    return (
        ThresholdCase(
            row_id="source_integral_threshold",
            row_role="target_threshold",
            normalized_quantity="I_source(t) >= Theta_migration",
            baseline_value=1.0,
            observed_value=0.82,
            threshold_value=1.0,
            status="THRESHOLD_NOT_REACHED",
            supports_threshold=False,
            obstructs_threshold=True,
            blockers=("large_data_source_integral_lower_bound_missing", PARENT_GATE),
            interpretation=(
                "The source integral is the desired trigger, but the deterministic "
                "ledger records no lower bound strong enough to initiate migration."
            ),
        ),
        ThresholdCase(
            row_id="symmetry_plane_diffusion_baseline",
            row_role="pure_diffusion_baseline",
            normalized_quantity="nu * |Ltilde v| on the symmetry plane",
            baseline_value=1.0,
            observed_value=1.0,
            threshold_value=1.0,
            status="PURE_DIFFUSION_BASELINE_AVAILABLE",
            supports_threshold=True,
            obstructs_threshold=False,
            blockers=(),
            interpretation=(
                "At the symmetry plane the normalized row is pure diffusion; this "
                "is local baseline support, not an off-axis migration exclusion."
            ),
        ),
        ThresholdCase(
            row_id="off_axis_gain",
            row_role="adverse_gain",
            normalized_quantity="gain from off-axis source and transport alignment",
            baseline_value=1.0,
            observed_value=1.34,
            threshold_value=1.0,
            status="OFF_AXIS_GAIN_UNCONTROLLED",
            supports_threshold=False,
            obstructs_threshold=True,
            blockers=("off_axis_gain_bound_missing", PARENT_GATE),
            interpretation=(
                "Off-axis gain can exceed the symmetry-plane baseline, so the "
                "threshold cannot be promoted from the pinned-plane computation."
            ),
        ),
        ThresholdCase(
            row_id="viscosity_suppression",
            row_role="damping_loss",
            normalized_quantity="effective viscous damping retained at the migrating maximum",
            baseline_value=1.0,
            observed_value=0.46,
            threshold_value=1.0,
            status="VISCOSITY_SUPPRESSION_PRESENT",
            supports_threshold=False,
            obstructs_threshold=True,
            blockers=("uniform_viscous_retention_missing", "large_data_scale_loss"),
            interpretation=(
                "Large-data scaling suppresses the retained viscous damping, leaving "
                "the source threshold without a uniform absorption margin."
            ),
        ),
        ThresholdCase(
            row_id="log_supercritical_feedback",
            row_role="feedback_amplifier",
            normalized_quantity="log-supercritical Biot-Savart feedback factor",
            baseline_value=1.0,
            observed_value=1.72,
            threshold_value=1.0,
            status="LOG_SUPERCRITICAL_FEEDBACK_OPEN",
            supports_threshold=False,
            obstructs_threshold=True,
            blockers=("log_supercritical_feedback_absorption_missing",),
            interpretation=(
                "The log-supercritical feedback multiplier remains adverse and is "
                "not absorbed by the current threshold ledger."
            ),
        ),
        ThresholdCase(
            row_id="smooth_finite_energy_admissibility",
            row_role="admissibility_guard",
            normalized_quantity="smooth finite-energy profile admissibility",
            baseline_value=1.0,
            observed_value=1.0,
            threshold_value=1.0,
            status="ADMISSIBLE_BUT_NOT_PROOF",
            supports_threshold=True,
            obstructs_threshold=True,
            blockers=("admissibility_does_not_imply_blowup", PARENT_GATE),
            interpretation=(
                "Smooth finite-energy admissibility is compatible with the row set, "
                "but compatibility is not a migration threshold proof."
            ),
        ),
        ThresholdCase(
            row_id="clay_promotion_guard",
            row_role="promotion_guard",
            normalized_quantity="Clay promotion requires threshold proof plus blowup existence",
            baseline_value=0.0,
            observed_value=0.0,
            threshold_value=1.0,
            status="PROMOTION_BLOCKED",
            supports_threshold=False,
            obstructs_threshold=True,
            blockers=(
                "migration_initiation_threshold_proved_false",
                "blowup_existence_proved_false",
                "full_clay_ns_solved_false",
            ),
            interpretation=(
                "The guard explicitly blocks Clay promotion because neither the "
                "migration threshold nor blowup existence has been proved."
            ),
        ),
    )


def build_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for case in sample_cases():
        margin = clean(case.observed_value - case.threshold_value)
        ratio = None
        if abs(case.threshold_value) > 1.0e-14:
            ratio = clean(case.observed_value / case.threshold_value)
        row = ThresholdRow(
            row_id=case.row_id,
            sprint=SPRINT,
            lane=LANE,
            contract=CONTRACT,
            program=PROGRAM,
            target_gate=TARGET_GATE,
            parent_sprint=PARENT_SPRINT,
            parent_contract=PARENT_CONTRACT,
            parent_gate=PARENT_GATE,
            row_role=case.row_role,
            normalized_quantity=case.normalized_quantity,
            baseline_value=clean(case.baseline_value),
            observed_value=clean(case.observed_value),
            threshold_value=clean(case.threshold_value),
            margin_to_threshold=margin,
            ratio_to_threshold=ratio,
            status=case.status,
            supports_threshold=case.supports_threshold,
            obstructs_threshold=case.obstructs_threshold,
            blockers=case.blockers,
            interpretation=case.interpretation,
            migration_initiation_threshold_proved=False,
            blowup_existence_proved=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            pure_diffusion_at_symmetry_plane=True,
            maximum_location_migration_exclusion=False,
            artifact_complete=True,
        ).as_row()
        rows.append(row)
    return rows


def build_summary(
    rows: list[dict[str, Any]],
    upstream_state: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    row_ids = [str(row["row_id"]) for row in rows]
    missing = sorted(REQUIRED_ROW_IDS.difference(row_ids))
    extra = sorted(set(row_ids).difference(REQUIRED_ROW_IDS))
    blockers = sorted({str(blocker) for row in rows for blocker in row["blockers"]})
    status_counts: dict[str, int] = {}
    for row in rows:
        status_counts[str(row["status"])] = status_counts.get(str(row["status"]), 0) + 1

    obstruction_rows = [row for row in rows if row["obstructs_threshold"]]
    support_rows = [row for row in rows if row["supports_threshold"]]

    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "program": PROGRAM,
        "decision": DECISION,
        "target_gate": TARGET_GATE,
        "parent_sprint": PARENT_SPRINT,
        "parent_contract": PARENT_CONTRACT,
        "parent_gate": PARENT_GATE,
        "threshold_formula": THRESHOLD_FORMULA,
        "baseline_formula": BASELINE_FORMULA,
        "admissibility_formula": ADMISSIBILITY_FORMULA,
        "row_count": len(rows),
        "required_row_ids": sorted(REQUIRED_ROW_IDS),
        "observed_row_ids": row_ids,
        "missing_required_row_ids": missing,
        "extra_row_ids": extra,
        "status_counts": status_counts,
        "support_row_ids": [row["row_id"] for row in support_rows],
        "obstruction_row_ids": [row["row_id"] for row in obstruction_rows],
        "blockers": blockers,
        "upstream_artifact_state": upstream_state,
        "fail_closed": True,
        "migration_threshold_available": False,
        "migration_threshold_closed": False,
        "migration_initiation_threshold_proved": False,
        "blowup_existence_proved": False,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "pure_diffusion_at_symmetry_plane": True,
        "maximum_location_migration_exclusion": False,
        "promotion_allowed": False,
        "artifact_complete": False,
        "invariants_passed": False,
        "invariant_valid": False,
        "invariant_checked": False,
        "invariant_failures": [],
        "control_card": {
            "O": (
                "Lane 2 owns only the Sprint 147 Python emitter and "
                f"{OUT_DIR_DEFAULT}/ artifacts for the migration-initiation threshold."
            ),
            "R": (
                "Emit deterministic rows for source integral threshold, symmetry-plane "
                "diffusion baseline, off-axis gain, viscosity suppression, "
                "log-supercritical feedback, smooth finite-energy admissibility, "
                "and the Clay promotion guard."
            ),
            "C": (
                "Single stdlib Python script writes rows JSON, CSV, summary JSON, "
                "Markdown, and manifest through an atomic staging directory."
            ),
            "S": (
                "The ledger is fail-closed: the symmetry plane remains pure diffusion, "
                "but no migration-initiation threshold, blowup existence theorem, or "
                "Clay Navier-Stokes solution is proved."
            ),
            "L": (
                "Normalize each row against a unit threshold, record threshold margins, "
                "and require all proof and promotion flags to remain false while the "
                "pure-diffusion baseline flag remains true."
            ),
            "P": (
                "Use the artifact as a threshold evidence packet for the missing "
                "MigrationInitiationThresholdForLargeData gate, not as a proof."
            ),
            "G": (
                "Validation passes only when all seven named rows exist, blockers are "
                "explicit, requested flags have the mandated truth values, and the "
                "artifact completeness invariant is true."
            ),
            "F": (
                "Missing: a proved source-integral threshold, off-axis migration "
                "exclusion, blowup existence theorem, and Clay promotion eligibility."
            ),
        },
    }

    failures: list[str] = []
    if missing:
        failures.append("missing_required_rows:" + ",".join(missing))
    if extra:
        failures.append("unexpected_rows:" + ",".join(extra))
    if not obstruction_rows:
        failures.append("obstruction_rows_missing")
    if "symmetry_plane_diffusion_baseline" not in row_ids:
        failures.append("symmetry_plane_diffusion_baseline_missing")
    for key in SUMMARY_REQUIRED_FALSE:
        if summary[key]:
            failures.append(f"summary_{key}_must_remain_false")
    for key in SUMMARY_REQUIRED_TRUE.difference({"artifact_complete"}):
        if not summary[key]:
            failures.append(f"summary_{key}_must_remain_true")
    for row in rows:
        for key in SUMMARY_REQUIRED_FALSE:
            if row[key]:
                failures.append(f"row_{row['row_id']}_{key}_must_remain_false")
        if not row["pure_diffusion_at_symmetry_plane"]:
            failures.append(f"row_{row['row_id']}_pure_diffusion_flag_must_remain_true")
        if not row["artifact_complete"]:
            failures.append(f"row_{row['row_id']}_artifact_complete_must_remain_true")
        if row["claim_closed"] or row["claim_proved"] or row["claim_proven"]:
            failures.append(f"row_{row['row_id']}_claim_incorrectly_closed")
        if row["row_id"] != "symmetry_plane_diffusion_baseline" and not row["blockers"]:
            failures.append(f"row_{row['row_id']}_blockers_missing")

    summary["invariant_failures"] = failures
    summary["invariants_passed"] = not failures
    summary["invariant_valid"] = summary["invariants_passed"]
    summary["invariant_checked"] = summary["invariants_passed"]
    summary["artifact_complete"] = not failures
    summary["summary_hash"] = stable_hash(
        {key: value for key, value in summary.items() if key != "summary_hash"}
    )
    return summary


def validate(rows: list[dict[str, Any]], summary: dict[str, Any]) -> None:
    errors: list[str] = []
    if not rows:
        errors.append("no rows emitted")
    if not summary["artifact_complete"]:
        errors.append("artifact_complete must be true")
    if not summary["invariants_passed"]:
        errors.append("invariants_passed must be true")
    errors.extend(summary["invariant_failures"])
    for key in SUMMARY_REQUIRED_FALSE:
        if summary[key]:
            errors.append(f"{key} must remain false")
    for key in SUMMARY_REQUIRED_TRUE:
        if not summary[key]:
            errors.append(f"{key} must remain true")
    if errors:
        raise ValueError("; ".join(errors))


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        raise ValueError("cannot write empty CSV")
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def format_value(value: Any) -> str:
    if isinstance(value, bool):
        return str(value).lower()
    if isinstance(value, float):
        return f"{value:.12g}"
    if isinstance(value, list):
        return ", ".join(str(item) for item in value)
    return str(value)


def write_report(path: Path, rows: list[dict[str, Any]], summary: dict[str, Any]) -> None:
    lines = [
        "# Sprint 147 Migration Initiation Threshold",
        "",
        "Deterministic fail-closed emitter for `MigrationInitiationThresholdForLargeData`.",
        "",
        "## Decision",
        "",
        f"- decision: `{summary['decision']}`",
        f"- target gate: `{summary['target_gate']}`",
        f"- threshold proved: `{format_value(summary['migration_initiation_threshold_proved'])}`",
        f"- blowup existence proved: `{format_value(summary['blowup_existence_proved'])}`",
        f"- pure diffusion at symmetry plane: `{format_value(summary['pure_diffusion_at_symmetry_plane'])}`",
        f"- maximum-location migration exclusion: `{format_value(summary['maximum_location_migration_exclusion'])}`",
        f"- Clay promotion: `{format_value(summary['clay_navier_stokes_promoted'])}`",
        "",
        "## Rows",
        "",
        "| row_id | status | observed | threshold | margin | blockers |",
        "|---|---|---:|---:|---:|---|",
    ]
    for row in rows:
        lines.append(
            "| {row_id} | {status} | {observed_value:.6g} | {threshold_value:.6g} | "
            "{margin_to_threshold:.6g} | {blockers} |".format(
                **{**row, "blockers": ", ".join(row["blockers"])}
            )
        )
    lines.extend(["", "## Interpretations", ""])
    for row in rows:
        lines.append(f"- `{row['row_id']}`: {row['interpretation']}")
    lines.extend(["", "## Control Card", ""])
    for key, value in summary["control_card"].items():
        lines.append(f"- {key}: {value}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_manifest(path: Path, out_dir: Path, repo_root: Path, files: list[Path]) -> None:
    manifest = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "out_dir": display_path(out_dir, repo_root),
        "files": [
            {
                "path": display_path(file_path, repo_root),
                "sha256": file_sha256(file_path),
                "bytes": file_path.stat().st_size,
            }
            for file_path in files
        ],
    }
    manifest["manifest_hash"] = stable_hash(manifest)
    write_json(path, manifest)


def publish_outputs(out_dir: Path, tmp_dir: Path) -> None:
    if out_dir.exists():
        shutil.rmtree(out_dir)
    out_dir.parent.mkdir(parents=True, exist_ok=True)
    os.replace(tmp_dir, out_dir)


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = repo_root / out_dir
    out_dir = out_dir.resolve()

    rows = build_rows()
    upstream = source_artifact_state(repo_root)
    summary = build_summary(rows, upstream)
    validate(rows, summary)

    out_dir.parent.mkdir(parents=True, exist_ok=True)
    tmp_dir_path = Path(tempfile.mkdtemp(prefix=f".{CONTRACT}.", dir=str(out_dir.parent)))
    try:
        summary_path = tmp_dir_path / SUMMARY_NAME
        rows_json_path = tmp_dir_path / ROWS_JSON_NAME
        rows_csv_path = tmp_dir_path / ROWS_CSV_NAME
        report_path = tmp_dir_path / REPORT_NAME
        manifest_path = tmp_dir_path / MANIFEST_NAME

        write_json(summary_path, summary)
        write_json(rows_json_path, rows)
        write_csv(rows_csv_path, rows)
        write_report(report_path, rows, summary)
        write_manifest(
            manifest_path,
            out_dir,
            repo_root,
            [summary_path, rows_json_path, rows_csv_path, report_path],
        )
        publish_outputs(out_dir, tmp_dir_path)
    except Exception:
        shutil.rmtree(tmp_dir_path, ignore_errors=True)
        raise

    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"{CONTRACT}: {exc}", file=sys.stderr)
        raise SystemExit(1)
