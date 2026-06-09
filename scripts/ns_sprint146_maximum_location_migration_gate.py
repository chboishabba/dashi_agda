#!/usr/bin/env python3
"""Sprint 146 maximum-location migration gate sampler.

This deterministic classifier records the new gate needed after the Sprint 145
comparison-envelope obstruction:

    MaximumLocationMigrationLemma

The missing lemma would have to control how a first positive maximum of
v = partial_z u1 moves when the nonlocal source

    2*u1*partial_z^2 psi1

and radial transport/commutator terms change sign away from the pinned symmetry
center.  The sampler is intentionally fail-closed: it emits support, blocker,
and partial-recovery rows, but proves no migration lemma, no global barrier, and
no Clay Navier-Stokes promotion.
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


CONTRACT = "ns_sprint146_maximum_location_migration_gate"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint146_maximum_location_migration_gate")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"
MANIFEST_NAME = CONTRACT + "_manifest.json"

SPRINT = 146
LANE = 4
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
TARGET_GATE = "MaximumLocationMigrationLemma"
TARGET_VARIABLE = "v = partial_z u1"
PARENT_SPRINT = 145
PARENT_CONTRACT = "ns_sprint145_comparison_envelope_inequality"
DECISION = "fail_closed_maximum_location_migration_gate_open"
MISSING_LEMMA = "MaximumLocationMigrationLemma"
MISSING_ENVELOPE = "ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators"
V_BARRIER_EQUATION = (
    "D_t v = nu Ltilde v + 2 v partial_z psi1 + 2 u1 partial_z^2 psi1 "
    "- (partial_z u^r) partial_r u1 - (partial_z u^z) v"
)
SOURCE_SIGN_FORMULA = "source_sign = sign(2*u1*partial_z^2 psi1)"
MIGRATION_PROXY_FORMULA = (
    "x_max_dot_proxy = -partial_space_source_proxy / max(-partial_space2_v_proxy, eps)"
)

REQUIRED_ROW_IDS = {
    "pinned_center",
    "symmetric_twin_peak_migration",
    "positive_feedback_candidate",
    "regularity_partial_recovery_branch",
}

SUMMARY_REQUIRED_FALSE = {
    "maximum_location_migration_lemma_proved",
    "migration_gate_closed",
    "comparison_envelope_available",
    "comparison_envelope_proved",
    "global_barrier_closed",
    "full_clay_ns_solved",
    "clay_navier_stokes_promoted",
    "promotion_allowed",
}

SOURCE_ARTIFACTS = {
    "sprint145_comparison_envelope_inequality": (
        "outputs/ns_sprint145_comparison_envelope_inequality/"
        "ns_sprint145_comparison_envelope_inequality_summary.json"
    ),
    "sprint145_source_commutator_alignment_sampler": (
        "outputs/ns_sprint145_source_commutator_alignment_sampler/"
        "ns_sprint145_source_commutator_alignment_sampler_summary.json"
    ),
}


@dataclass(frozen=True)
class MigrationCase:
    row_id: str
    scenario: str
    location_class: str
    u1: float
    partial_z2_psi1_proxy: float
    partial_space_source_proxy: float
    partial_space2_v_proxy: float
    radial_drift_proxy: float
    regularity_budget_proxy: float
    expected_source_sign: str
    expected_migration_class: str
    status: str
    blockers: tuple[str, ...]
    source_sign_logic: str
    interpretation: str


@dataclass(frozen=True)
class MigrationRow:
    row_id: str
    sprint: int
    lane: int
    contract: str
    program: str
    target_gate: str
    target_variable: str
    parent_sprint: int
    parent_contract: str
    scenario: str
    location_class: str
    u1: float
    partial_z2_psi1_proxy: float
    partial_space_source_proxy: float
    partial_space2_v_proxy: float
    radial_drift_proxy: float
    regularity_budget_proxy: float
    source_term_proxy: float
    source_sign: str
    source_sign_matches_expected: bool
    maximum_location_velocity_proxy: float
    migration_pressure_proxy: float
    migration_classification: str
    status: str
    blockers: tuple[str, ...]
    source_sign_logic: str
    supports_pinned_center_only: bool
    symmetric_migration_row: bool
    positive_feedback_row: bool
    regularity_partial_recovery_row: bool
    obstructs_migration_gate: bool
    maximum_location_migration_lemma_proved: bool
    migration_gate_closed: bool
    comparison_envelope_available: bool
    comparison_envelope_proved: bool
    global_barrier_closed: bool
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool
    promotion_allowed: bool
    interpretation: str

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row["blockers"] = list(row["blockers"])
        row["decision"] = DECISION
        row["missing_lemma"] = MISSING_LEMMA
        row["missing_comparison_envelope"] = MISSING_ENVELOPE
        row["v_barrier_equation"] = V_BARRIER_EQUATION
        row["source_sign_formula"] = SOURCE_SIGN_FORMULA
        row["migration_proxy_formula"] = MIGRATION_PROXY_FORMULA
        row["claim_closed"] = False
        row["claim_proved"] = False
        row["claim_proven"] = False
        row["no_global_proof"] = True
        row["no_promotion"] = True
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


def sign(value: float) -> str:
    if value > 1.0e-12:
        return "positive"
    if value < -1.0e-12:
        return "negative"
    return "zero"


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
                "comparison_envelope_available",
                "comparison_envelope_proved",
                "global_alignment_theorem_proved",
                "global_barrier_closed",
                "full_clay_ns_solved",
                "clay_navier_stokes_promoted",
            ):
                if flag in payload:
                    entry[flag] = payload[flag]
        state[key] = entry
    return state


def sample_cases() -> tuple[MigrationCase, ...]:
    return (
        MigrationCase(
            row_id="pinned_center",
            scenario="symmetry_center_first_maximum_remains_pinned",
            location_class="center",
            u1=1.0,
            partial_z2_psi1_proxy=-0.38,
            partial_space_source_proxy=0.0,
            partial_space2_v_proxy=-1.0,
            radial_drift_proxy=0.0,
            regularity_budget_proxy=0.82,
            expected_source_sign="negative",
            expected_migration_class="pinned_local_support",
            status="SUPPORT_LOCAL_ONLY",
            blockers=(MISSING_LEMMA, "off_center_first_maximum_exclusion_missing"),
            source_sign_logic=(
                "u1 is positive and partial_z^2 psi1 is negative at the symmetry center, "
                "so 2*u1*partial_z^2 psi1 damps v locally."
            ),
            interpretation=(
                "The pinned center row supports the route only while the maximum stays "
                "on the symmetry-center patch; it does not prevent migration."
            ),
        ),
        MigrationCase(
            row_id="symmetric_twin_peak_migration",
            scenario="two_equal_off_center_shoulders_compete_for_maximum",
            location_class="symmetric_twin_peak",
            u1=0.92,
            partial_z2_psi1_proxy=-0.06,
            partial_space_source_proxy=0.34,
            partial_space2_v_proxy=-0.48,
            radial_drift_proxy=0.19,
            regularity_budget_proxy=0.57,
            expected_source_sign="negative",
            expected_migration_class="migrating_twin_peak_branch",
            status="BLOCKED_BY_MAXIMUM_LOCATION_MIGRATION",
            blockers=(MISSING_LEMMA, "tie_breaking_for_symmetric_twin_peaks_missing"),
            source_sign_logic=(
                "The pointwise source is weakly negative because partial_z^2 psi1 "
                "is weakly negative at each shoulder, but the spatial derivative "
                "of the source is nonzero, so the maximizing location can drift "
                "before a scalar maximum-principle argument closes."
            ),
            interpretation=(
                "A favorable pointwise sign does not identify one persistent maximum "
                "curve across symmetric twin peaks."
            ),
        ),
        MigrationCase(
            row_id="positive_feedback_candidate",
            scenario="off_center_candidate_with_positive_nonlocal_feedback",
            location_class="off_center_feedback",
            u1=0.78,
            partial_z2_psi1_proxy=0.27,
            partial_space_source_proxy=-0.22,
            partial_space2_v_proxy=-0.41,
            radial_drift_proxy=0.24,
            regularity_budget_proxy=0.49,
            expected_source_sign="positive",
            expected_migration_class="wrong_sign_feedback_migration",
            status="BLOCKED_BY_POSITIVE_SOURCE_FEEDBACK",
            blockers=(MISSING_LEMMA, MISSING_ENVELOPE, "positive_source_sign_not_absorbed"),
            source_sign_logic=(
                "u1 is positive and partial_z^2 psi1 is positive, so "
                "2*u1*partial_z^2 psi1 reinforces v at the candidate maximum."
            ),
            interpretation=(
                "The row records the adverse source-sign branch that a migration lemma "
                "would have to rule out or absorb."
            ),
        ),
        MigrationCase(
            row_id="regularity_partial_recovery_branch",
            scenario="regularity_budget_bounds_drift_but_not_sign",
            location_class="regularity_recovery",
            u1=0.66,
            partial_z2_psi1_proxy=0.04,
            partial_space_source_proxy=0.08,
            partial_space2_v_proxy=-0.72,
            radial_drift_proxy=0.05,
            regularity_budget_proxy=0.93,
            expected_source_sign="positive",
            expected_migration_class="partial_recovery_not_closure",
            status="PARTIAL_RECOVERY_BLOCKED",
            blockers=(MISSING_LEMMA, "regularity_budget_does_not_supply_source_sign"),
            source_sign_logic=(
                "Regularity keeps drift small, but the source sign is still determined "
                "by partial_z^2 psi1; a small positive value remains positive feedback."
            ),
            interpretation=(
                "The regularity branch can reduce migration speed without closing the "
                "source-sign or comparison-envelope obligation."
            ),
        ),
    )


def classify_migration(
    case: MigrationCase,
    source_term: float,
    velocity: float,
    migration_pressure: float,
) -> str:
    if case.row_id == "pinned_center" and sign(source_term) == "negative" and abs(velocity) < 1.0e-12:
        return "pinned_center_damping_support_only"
    if case.row_id == "regularity_partial_recovery_branch":
        return "regularity_reduces_drift_but_source_sign_open"
    if sign(source_term) == "positive":
        return "positive_feedback_migration_obstruction"
    if abs(velocity) > 0.25 or migration_pressure > 0.3:
        return "source_gradient_drives_maximum_migration"
    return "weak_migration_obstruction"


def build_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    eps = 1.0e-12
    for case in sample_cases():
        source_term = 2.0 * case.u1 * case.partial_z2_psi1_proxy
        velocity = (
            -case.partial_space_source_proxy / max(-case.partial_space2_v_proxy, eps)
            + case.radial_drift_proxy
        )
        migration_pressure = abs(velocity) * (1.0 - min(case.regularity_budget_proxy, 1.0))
        classification = classify_migration(case, source_term, velocity, migration_pressure)
        row = MigrationRow(
            row_id=case.row_id,
            sprint=SPRINT,
            lane=LANE,
            contract=CONTRACT,
            program=PROGRAM,
            target_gate=TARGET_GATE,
            target_variable=TARGET_VARIABLE,
            parent_sprint=PARENT_SPRINT,
            parent_contract=PARENT_CONTRACT,
            scenario=case.scenario,
            location_class=case.location_class,
            u1=case.u1,
            partial_z2_psi1_proxy=case.partial_z2_psi1_proxy,
            partial_space_source_proxy=case.partial_space_source_proxy,
            partial_space2_v_proxy=case.partial_space2_v_proxy,
            radial_drift_proxy=case.radial_drift_proxy,
            regularity_budget_proxy=case.regularity_budget_proxy,
            source_term_proxy=clean(source_term),
            source_sign=sign(source_term),
            source_sign_matches_expected=sign(source_term) == case.expected_source_sign,
            maximum_location_velocity_proxy=clean(velocity),
            migration_pressure_proxy=clean(migration_pressure),
            migration_classification=classification,
            status=case.status,
            blockers=case.blockers,
            source_sign_logic=case.source_sign_logic,
            supports_pinned_center_only=case.row_id == "pinned_center",
            symmetric_migration_row=case.row_id == "symmetric_twin_peak_migration",
            positive_feedback_row=case.row_id == "positive_feedback_candidate",
            regularity_partial_recovery_row=case.row_id == "regularity_partial_recovery_branch",
            obstructs_migration_gate=case.row_id != "pinned_center",
            maximum_location_migration_lemma_proved=False,
            migration_gate_closed=False,
            comparison_envelope_available=False,
            comparison_envelope_proved=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
            interpretation=case.interpretation,
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

    positive_source_rows = [row for row in rows if row["source_sign"] == "positive"]
    negative_source_rows = [row for row in rows if row["source_sign"] == "negative"]
    migration_rows = [
        row
        for row in rows
        if abs(float(row["maximum_location_velocity_proxy"])) > 1.0e-12
    ]
    obstruction_rows = [row for row in rows if row["obstructs_migration_gate"]]

    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "program": PROGRAM,
        "decision": DECISION,
        "target_gate": TARGET_GATE,
        "target_variable": TARGET_VARIABLE,
        "parent_sprint": PARENT_SPRINT,
        "parent_contract": PARENT_CONTRACT,
        "missing_lemma": MISSING_LEMMA,
        "missing_comparison_envelope": MISSING_ENVELOPE,
        "source_sign_formula": SOURCE_SIGN_FORMULA,
        "migration_proxy_formula": MIGRATION_PROXY_FORMULA,
        "v_barrier_equation": V_BARRIER_EQUATION,
        "row_count": len(rows),
        "required_row_ids": sorted(REQUIRED_ROW_IDS),
        "observed_row_ids": row_ids,
        "missing_required_row_ids": missing,
        "extra_row_ids": extra,
        "status_counts": status_counts,
        "blockers": blockers,
        "positive_source_row_ids": [row["row_id"] for row in positive_source_rows],
        "negative_source_row_ids": [row["row_id"] for row in negative_source_rows],
        "migration_row_ids": [row["row_id"] for row in migration_rows],
        "obstruction_row_ids": [row["row_id"] for row in obstruction_rows],
        "has_pinned_center_row": any(row["row_id"] == "pinned_center" for row in rows),
        "has_symmetric_twin_peak_migration_row": any(
            row["row_id"] == "symmetric_twin_peak_migration" for row in rows
        ),
        "has_positive_feedback_candidate_row": any(
            row["row_id"] == "positive_feedback_candidate" for row in rows
        ),
        "has_regularity_partial_recovery_branch_row": any(
            row["row_id"] == "regularity_partial_recovery_branch" for row in rows
        ),
        "has_positive_source_sign": bool(positive_source_rows),
        "has_negative_source_sign": bool(negative_source_rows),
        "has_migration_velocity": bool(migration_rows),
        "has_blockers": bool(blockers),
        "upstream_artifact_state": upstream_state,
        "fail_closed": True,
        "maximum_location_migration_lemma_proved": False,
        "migration_gate_closed": False,
        "comparison_envelope_available": False,
        "comparison_envelope_proved": False,
        "global_barrier_closed": False,
        "global_proof": False,
        "global_proof_closed": False,
        "no_global_proof": True,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "promotion_allowed": False,
        "no_promotion": True,
        "artifact_complete": False,
        "invariants_passed": False,
        "invariant_valid": False,
        "invariant_checked": False,
        "invariant_failures": [],
        "control_card": {
            "O": (
                "Lane 4 owns only Python sprint script/test surfaces and generated "
                f"{OUT_DIR_DEFAULT}/ artifacts for the Sprint 146 migration gate."
            ),
            "R": (
                "Emit deterministic rows for pinned_center, symmetric_twin_peak_migration, "
                "positive_feedback_candidate, and regularity_partial_recovery_branch."
            ),
            "C": (
                "Single stdlib Python sampler writes summary JSON, rows JSON, CSV, "
                "Markdown, and manifest through an atomic staging directory."
            ),
            "S": (
                "The migration gate remains open: local pinned damping exists, but "
                "off-center migration, positive feedback, and partial regularity rows block closure."
            ),
            "L": (
                "Compute source sign from 2*u1*partial_z^2 psi1, combine source-gradient "
                "and radial-drift proxies, classify migration status, then fail closed."
            ),
            "P": (
                "Use the rows as a deterministic evidence packet for the missing "
                "MaximumLocationMigrationLemma rather than as a proof artifact."
            ),
            "G": (
                "Validation passes only when all four named rows exist, source sign "
                "logic covers positive and negative branches, blockers are explicit, "
                "and all theorem/promotion flags remain false."
            ),
            "F": (
                f"Missing: {MISSING_LEMMA}; downstream comparison envelope, global "
                "barrier closure, and Clay promotion remain unavailable."
            ),
        },
    }

    failures: list[str] = []
    if missing:
        failures.append("missing_required_rows:" + ",".join(missing))
    if extra:
        failures.append("unexpected_rows:" + ",".join(extra))
    if not positive_source_rows:
        failures.append("positive_source_sign_rows_missing")
    if not negative_source_rows:
        failures.append("negative_source_sign_rows_missing")
    if not migration_rows:
        failures.append("migration_velocity_rows_missing")
    if not blockers:
        failures.append("blockers_missing")
    for key in SUMMARY_REQUIRED_FALSE:
        if summary[key]:
            failures.append(f"summary_{key}_must_remain_false")
    for row in rows:
        for key in SUMMARY_REQUIRED_FALSE:
            if row[key]:
                failures.append(f"row_{row['row_id']}_{key}_must_remain_false")
        if not row["source_sign_matches_expected"]:
            failures.append(f"row_{row['row_id']}_source_sign_mismatch")
        if not row["source_sign_logic"]:
            failures.append(f"row_{row['row_id']}_source_sign_logic_missing")
        if not row["blockers"]:
            failures.append(f"row_{row['row_id']}_blockers_missing")
        if row["claim_closed"] or row["claim_proved"] or row["claim_proven"]:
            failures.append(f"row_{row['row_id']}_claim_incorrectly_closed")

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
    if summary["invariant_failures"]:
        errors.extend(summary["invariant_failures"])
    for key in SUMMARY_REQUIRED_FALSE:
        if summary[key]:
            errors.append(f"{key} must remain false")
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
        "# Sprint 146 Maximum-Location Migration Gate",
        "",
        "Deterministic fail-closed sampler for `MaximumLocationMigrationLemma`.",
        "",
        "## Decision",
        "",
        f"- decision: `{summary['decision']}`",
        f"- missing lemma: `{summary['missing_lemma']}`",
        f"- source sign formula: `{summary['source_sign_formula']}`",
        f"- migration gate closed: `{format_value(summary['migration_gate_closed'])}`",
        f"- Clay promotion: `{format_value(summary['clay_navier_stokes_promoted'])}`",
        "",
        "## Rows",
        "",
        "| row_id | status | source_sign | source | x_max_dot | blockers |",
        "|---|---|---:|---:|---:|---|",
    ]
    for row in rows:
        lines.append(
            "| {row_id} | {status} | {source_sign} | {source_term_proxy:.6g} | "
            "{maximum_location_velocity_proxy:.6g} | {blockers} |".format(
                **{**row, "blockers": ", ".join(row["blockers"])}
            )
        )
    lines.extend(["", "## Source Sign Logic", ""])
    for row in rows:
        lines.append(f"- `{row['row_id']}`: {row['source_sign_logic']}")
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
