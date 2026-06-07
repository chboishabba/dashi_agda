#!/usr/bin/env python3
"""Sprint 144 nonlocal source zero-number failure ledger.

This deterministic ledger records why the scalar zero-number/Sturm transfer
does not close for v = partial_z u1 in the Hou-Luo axisymmetric-with-swirl
barrier route when the differentiated equation contains nonlocal psi1 source
terms and radial commutators.

The artifact is intentionally fail-closed.  It emits no comparison envelope,
does not prove the coupled zero-number theorem, does not exclude secondary
peaks, does not close the global barrier, and does not promote a Clay
Navier-Stokes solution.
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


CONTRACT = "ns_sprint144_nonlocal_source_zero_number_failure"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint144_nonlocal_source_zero_number_failure")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"
MANIFEST_NAME = CONTRACT + "_manifest.json"

SPRINT = 144
LANE = 4
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
TARGET_GATE = "ScalarZeroNumberTransferForVBarrier"
TARGET_VARIABLE = "v = partial_z u1"
MISSING_THEOREM = "CoupledAxisymmetricZeroNumberForVBarrier"
MISSING_ENVELOPE = "ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators"
DECISION = "fail_closed_nonlocal_source_zero_number_control_unavailable"
U1_EQUATION = "D_t u1 = 2 u1 partial_z psi1 + nu Ltilde u1"
V_BARRIER_EQUATION = (
    "D_t v = nu Ltilde v + 2 v partial_z psi1 + 2 u1 partial_z^2 psi1 "
    "- (partial_z u^r) partial_r u1 - (partial_z u^z) v"
)

REQUIRED_ROW_IDS = {
    "sign_changing_partial_z2_psi1",
    "off_peak_nonlocal_source",
    "radial_commutator_zero_creation",
    "log_biot_savart_hazard",
    "comparison_envelope_absent",
    "secondary_peak_exclusion_unproved",
}

SUMMARY_REQUIRED_FALSE = {
    "nonlocal_source_zero_number_control",
    "comparison_envelope_available",
    "coupled_zero_number_theorem_proved",
    "secondary_peak_exclusion_proved",
    "global_barrier_closed",
    "full_clay_ns_solved",
    "clay_navier_stokes_promoted",
}

SOURCE_ARTIFACTS = {
    "sprint141_radial_gradient_coupling": (
        "outputs/ns_sprint141_radial_gradient_coupling_ledger/"
        "ns_sprint141_radial_gradient_coupling_ledger_summary.json"
    ),
    "sprint141_log_commutator": (
        "outputs/ns_sprint141_biot_savart_log_commutator_sampler/"
        "ns_sprint141_biot_savart_log_commutator_sampler_summary.json"
    ),
    "sprint142_boundary_annulus": (
        "outputs/ns_sprint142_boundary_annulus_concavity_ledger/"
        "ns_sprint142_boundary_annulus_concavity_ledger_summary.json"
    ),
    "sprint143_secondary_peak": (
        "outputs/ns_sprint143_secondary_peak_exclusion_ledger/"
        "ns_sprint143_secondary_peak_exclusion_ledger_summary.json"
    ),
    "sprint143_zero_number": (
        "outputs/ns_sprint143_zero_number_obstruction/"
        "ns_sprint143_zero_number_obstruction_summary.json"
    ),
}


@dataclass(frozen=True)
class FailureRow:
    row_id: str
    layer: str
    obstruction_role: str
    scalar_zero_number_requirement: str
    coupled_v_barrier_feature: str
    failure_mechanism: tuple[str, ...]
    missing_input: tuple[str, ...]
    zero_number_consequence: str
    nonlocal_source_zero_number_control: bool
    comparison_envelope_available: bool
    coupled_zero_number_theorem_proved: bool
    secondary_peak_exclusion_proved: bool
    global_barrier_closed: bool
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool
    status: str

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row["failure_mechanism"] = list(self.failure_mechanism)
        row["missing_input"] = list(self.missing_input)
        row["program"] = PROGRAM
        row["target_gate"] = TARGET_GATE
        row["target_variable"] = TARGET_VARIABLE
        row["missing_theorem"] = MISSING_THEOREM
        row["missing_comparison_envelope"] = MISSING_ENVELOPE
        row["u1_equation"] = U1_EQUATION
        row["v_barrier_equation"] = V_BARRIER_EQUATION
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


def file_sha256(path: Path) -> str:
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


def read_source_artifact_state(repo_root: Path) -> dict[str, dict[str, Any]]:
    state: dict[str, dict[str, Any]] = {}
    for key, relative in SOURCE_ARTIFACTS.items():
        path = repo_root / relative
        entry: dict[str, Any] = {
            "path": relative,
            "exists": path.exists(),
            "sha256": file_sha256(path) if path.exists() else None,
        }
        if path.exists():
            try:
                payload = json.loads(path.read_text(encoding="utf-8"))
            except json.JSONDecodeError:
                payload = {}
            for flag in (
                "global_barrier_closed",
                "global_concavity_closed",
                "secondary_peak_exclusion_proved",
                "coupled_zero_number_theorem_available",
                "log_aware_commutator_domination_proved",
                "clay_navier_stokes_promoted",
            ):
                if flag in payload:
                    entry[flag] = payload[flag]
        state[key] = entry
    return state


def build_rows() -> list[dict[str, Any]]:
    rows = [
        FailureRow(
            row_id="sign_changing_partial_z2_psi1",
            layer="nonlocal_elliptic_source",
            obstruction_role="sign_indefinite_source",
            scalar_zero_number_requirement=(
                "A scalar zero-number transfer needs a closed one-dimensional "
                "parabolic equation whose forcing cannot create new sign changes "
                "outside the theorem hypotheses."
            ),
            coupled_v_barrier_feature=(
                "The v equation contains 2 u1 partial_z^2 psi1, where psi1 is "
                "determined by the global axisymmetric elliptic/Biot-Savart solve."
            ),
            failure_mechanism=(
                "partial_z^2 psi1 is not globally signed",
                "favorable local concavity near the main peak does not control all r-z points",
                "the source can have the sign needed to raise v where the scalar template expects damping",
            ),
            missing_input=(
                "global sign or domination theorem for partial_z^2 psi1",
                MISSING_ENVELOPE,
                MISSING_THEOREM,
            ),
            zero_number_consequence=(
                "The source term can move, preserve, or create axial sign changes; "
                "scalar zero-number monotonicity does not transfer."
            ),
            nonlocal_source_zero_number_control=False,
            comparison_envelope_available=False,
            coupled_zero_number_theorem_proved=False,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            status="sign_changing_source_uncontrolled",
        ),
        FailureRow(
            row_id="off_peak_nonlocal_source",
            layer="off_route_source_geometry",
            obstruction_role="secondary_shoulder_source",
            scalar_zero_number_requirement=(
                "The scalar route needs off-peak forcing to be either absent, "
                "ordered by a comparison envelope, or absorbed by a signed residual."
            ),
            coupled_v_barrier_feature=(
                "Off-peak omega1 or u1 mass can feed psi1 nonlocally and affect "
                "v away from the primary monitored peak."
            ),
            failure_mechanism=(
                "elliptic feedback is not localized to the primary axial peak",
                "off-route source mass can support a secondary positive shoulder",
                "annular and boundary contributions are not excluded by local peak data",
            ),
            missing_input=(
                "off-peak source exclusion theorem",
                "annular/boundary-compatible nonlocal comparison estimate",
                MISSING_ENVELOPE,
            ),
            zero_number_consequence=(
                "A secondary positive local maximum can remain compatible with "
                "the available ledgers, so zero-number transfer cannot exclude it."
            ),
            nonlocal_source_zero_number_control=False,
            comparison_envelope_available=False,
            coupled_zero_number_theorem_proved=False,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            status="off_peak_source_hazard_open",
        ),
        FailureRow(
            row_id="radial_commutator_zero_creation",
            layer="radial_transport_commutator",
            obstruction_role="non_scalar_commutator",
            scalar_zero_number_requirement=(
                "A one-dimensional zero-number proof needs transport and reaction "
                "terms that preserve the scalar sign-change argument."
            ),
            coupled_v_barrier_feature=(
                "The differentiated equation includes -(partial_z u^r) partial_r u1 "
                "and radial diffusion through Ltilde."
            ),
            failure_mechanism=(
                "partial_r u1 is not controlled by an axial zero count",
                "partial_z u^r is coupled to the global velocity field",
                "the commutator can inject the wrong sign at an off-route crossing",
            ),
            missing_input=(
                "radial-gradient coupling theorem at candidate v crossings",
                "commutator domination constants",
                MISSING_THEOREM,
            ),
            zero_number_consequence=(
                "Radial commutators can invalidate the scalar closed-equation "
                "hypothesis and can support new axial sign structure."
            ),
            nonlocal_source_zero_number_control=False,
            comparison_envelope_available=False,
            coupled_zero_number_theorem_proved=False,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            status="radial_commutator_unabsorbed",
        ),
        FailureRow(
            row_id="log_biot_savart_hazard",
            layer="biot_savart_kernel",
            obstruction_role="log_loss_hazard",
            scalar_zero_number_requirement=(
                "The scalar transfer needs coefficient and commutator budgets "
                "that stay within a fixed comparison envelope."
            ),
            coupled_v_barrier_feature=(
                "Near-coincident rings or grazing annuli can amplify partial_z u^r "
                "through a logarithmic Biot-Savart kernel effect."
            ),
            failure_mechanism=(
                "log amplification is compatible with the earlier hazard sampler",
                "no log-aware commutator theorem is available",
                "a local bounded ledger does not dominate unresolved near-coincident scales",
            ),
            missing_input=(
                "LogAwareCommutatorDominationForVBarrier",
                "uniform log-loss absorption constants",
                MISSING_ENVELOPE,
            ),
            zero_number_consequence=(
                "The comparison budget can fail before a scalar zero-number "
                "contradiction is reached."
            ),
            nonlocal_source_zero_number_control=False,
            comparison_envelope_available=False,
            coupled_zero_number_theorem_proved=False,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            status="log_biot_savart_hazard_open",
        ),
        FailureRow(
            row_id="comparison_envelope_absent",
            layer="comparison_interface",
            obstruction_role="missing_envelope",
            scalar_zero_number_requirement=(
                "To transfer zero-number control, all nonlocal source, radial, "
                "boundary, and commutator terms must fit into a common comparison envelope."
            ),
            coupled_v_barrier_feature=(
                "The available ledgers isolate separate hazards but do not supply "
                "one envelope that covers every admissible first crossing."
            ),
            failure_mechanism=(
                "no single residual inequality dominates partial_z^2 psi1 and commutators",
                "constants are not shown compatible across radial, annular, and log hazards",
                "the scalar equation used for comparison is not available",
            ),
            missing_input=(
                MISSING_ENVELOPE,
                "constant compatibility ledger with a positive residual margin",
                MISSING_THEOREM,
            ),
            zero_number_consequence=(
                "There is no certified scalar comparison problem whose zero-number "
                "decay can be imported into the coupled v dynamics."
            ),
            nonlocal_source_zero_number_control=False,
            comparison_envelope_available=False,
            coupled_zero_number_theorem_proved=False,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            status="comparison_envelope_missing",
        ),
        FailureRow(
            row_id="secondary_peak_exclusion_unproved",
            layer="barrier_gate",
            obstruction_role="promotion_blocker",
            scalar_zero_number_requirement=(
                "A successful transfer would prove no secondary axial peak, "
                "shoulder, or off-route positive local maximum of v appears."
            ),
            coupled_v_barrier_feature=(
                "The actual v barrier remains subject to sign-changing nonlocal "
                "source, radial commutator, log-kernel, boundary, and annular hazards."
            ),
            failure_mechanism=(
                "the coupled zero-number theorem is not proved",
                "secondary peak exclusion remains open",
                "global barrier closure and Clay promotion are therefore blocked",
            ),
            missing_input=(
                MISSING_THEOREM,
                MISSING_ENVELOPE,
                "formal secondary peak exclusion theorem for the monitored interval",
            ),
            zero_number_consequence=(
                "The Sprint 144 lane must remain fail-closed and cannot promote "
                "the scalar zero-number route."
            ),
            nonlocal_source_zero_number_control=False,
            comparison_envelope_available=False,
            coupled_zero_number_theorem_proved=False,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            status="required_theorem_missing_fail_closed",
        ),
    ]
    return [row.as_row() for row in rows]


def build_summary(rows: list[dict[str, Any]], source_state: dict[str, dict[str, Any]]) -> dict[str, Any]:
    row_ids = [row["row_id"] for row in rows]
    missing = sorted(REQUIRED_ROW_IDS.difference(row_ids))
    extra = sorted(set(row_ids).difference(REQUIRED_ROW_IDS))
    hazard_rows = [
        row["row_id"]
        for row in rows
        if row["status"].endswith("_open") or "missing" in row["status"]
    ]

    summary = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "program": PROGRAM,
        "decision": DECISION,
        "target_gate": TARGET_GATE,
        "target_variable": TARGET_VARIABLE,
        "missing_theorem": MISSING_THEOREM,
        "missing_comparison_envelope": MISSING_ENVELOPE,
        "u1_equation": U1_EQUATION,
        "v_barrier_equation": V_BARRIER_EQUATION,
        "row_count": len(rows),
        "required_row_ids": sorted(REQUIRED_ROW_IDS),
        "observed_row_ids": row_ids,
        "missing_required_row_ids": missing,
        "extra_row_ids": extra,
        "hazard_rows": hazard_rows,
        "source_artifact_state": source_state,
        "sign_changing_partial_z2_psi1_recorded": True,
        "off_peak_source_recorded": True,
        "radial_commutator_recorded": True,
        "log_biot_savart_hazard_recorded": True,
        "nonlocal_source_zero_number_control": False,
        "comparison_envelope_available": False,
        "comparison_envelope_exists": False,
        "comparison_envelope_constructed": False,
        "coupled_zero_number_theorem_proved": False,
        "coupled_zero_number_proved": False,
        "coupled_zero_number_theorem_available": False,
        "secondary_peak_exclusion_proved": False,
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
                "Worker lane 4 owns only scripts/ns_sprint144_nonlocal_source_zero_number_failure.py "
                "and outputs/ns_sprint144_nonlocal_source_zero_number_failure/."
            ),
            "R": (
                "Record why nonlocal psi1 source and commutator terms break scalar "
                "zero-number transfer for v = partial_z u1."
            ),
            "C": (
                "Deterministic Python ledger/sampler emitting summary JSON, row JSON, "
                "CSV, Markdown, and manifest through an atomic temp staging directory."
            ),
            "S": (
                "partial_z^2 psi1 is sign-changing, off-peak source remains live, "
                "radial commutators and log Biot-Savart hazards are unabsorbed, and "
                "no comparison envelope is available."
            ),
            "L": (
                "Scalar zero-number template -> nonlocal source gaps -> radial/log "
                "commutator gaps -> no comparison envelope -> no coupled theorem."
            ),
            "P": (
                "Use as a fail-closed obstruction ledger only; do not use as a "
                "comparison proof or zero-number theorem."
            ),
            "G": (
                "Validation passes only if all proof, envelope, barrier, Clay, and "
                "promotion flags remain false while artifact_complete is true."
            ),
            "F": (
                f"Missing: {MISSING_THEOREM} and {MISSING_ENVELOPE}; secondary peak "
                "exclusion, global barrier closure, and Clay Navier-Stokes promotion remain false."
            ),
        },
    }

    failures: list[str] = []
    if missing:
        failures.append("missing_required_rows:" + ",".join(missing))
    if extra:
        failures.append("unexpected_rows:" + ",".join(extra))
    for key in SUMMARY_REQUIRED_FALSE:
        if summary[key]:
            failures.append(f"summary_{key}_must_remain_false")
    for row in rows:
        for key in SUMMARY_REQUIRED_FALSE:
            if row[key]:
                failures.append(f"row_{row['row_id']}_{key}_must_remain_false")
        if row["claim_closed"] or row["claim_proved"] or row["claim_proven"]:
            failures.append(f"row_{row['row_id']}_claim_incorrectly_closed")
        if row["promotion_allowed"]:
            failures.append(f"row_{row['row_id']}_promotion_allowed")
    rows_blob = json.dumps(rows, sort_keys=True)
    for required_text in (
        "partial_z^2 psi1",
        "off-peak",
        "commutator",
        "Biot-Savart",
        MISSING_ENVELOPE,
        MISSING_THEOREM,
    ):
        if required_text not in rows_blob and required_text not in json.dumps(summary, sort_keys=True):
            failures.append("missing_required_text:" + required_text)

    summary["invariant_failures"] = failures
    summary["invariants_passed"] = not failures
    summary["invariant_valid"] = summary["invariants_passed"]
    summary["invariant_checked"] = summary["invariants_passed"]
    summary["artifact_complete"] = not failures
    summary["summary_hash"] = stable_hash(
        {k: v for k, v in summary.items() if k != "summary_hash"}
    )
    return summary


def validate(rows: list[dict[str, Any]], summary: dict[str, Any]) -> None:
    errors: list[str] = []
    if not rows:
        errors.append("no rows emitted")
    for key in SUMMARY_REQUIRED_FALSE:
        if summary[key]:
            errors.append(f"{key} must remain false")
    if not summary["artifact_complete"]:
        errors.append("artifact_complete must be true")
    if not summary["invariants_passed"]:
        errors.append("invariants_passed must be true")
    if summary["missing_required_row_ids"]:
        errors.append(f"missing rows: {summary['missing_required_row_ids']}")
    if summary["extra_row_ids"]:
        errors.append(f"unexpected rows: {summary['extra_row_ids']}")
    if summary["invariant_failures"]:
        errors.extend(summary["invariant_failures"])
    if errors:
        raise ValueError("; ".join(errors))


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        raise ValueError("cannot write empty row set")
    fieldnames = list(rows[0].keys())
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow(
                {
                    key: json.dumps(value, sort_keys=True)
                    if isinstance(value, (list, dict))
                    else value
                    for key, value in row.items()
                }
            )


def write_markdown(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    lines = [
        f"# {CONTRACT}",
        "",
        "## Decision",
        "",
        f"- Decision: `{summary['decision']}`",
        f"- Target gate: `{summary['target_gate']}`",
        f"- Target variable: `{summary['target_variable']}`",
        f"- Missing theorem: `{summary['missing_theorem']}`",
        f"- Missing comparison envelope: `{summary['missing_comparison_envelope']}`",
        f"- Nonlocal source zero-number control: `{summary['nonlocal_source_zero_number_control']}`",
        f"- Comparison envelope available: `{summary['comparison_envelope_available']}`",
        f"- Coupled zero-number theorem proved: `{summary['coupled_zero_number_theorem_proved']}`",
        f"- Secondary peak exclusion proved: `{summary['secondary_peak_exclusion_proved']}`",
        f"- Global barrier closed: `{summary['global_barrier_closed']}`",
        f"- Full Clay NS solved: `{summary['full_clay_ns_solved']}`",
        f"- Clay Navier-Stokes promoted: `{summary['clay_navier_stokes_promoted']}`",
        f"- Artifact complete: `{summary['artifact_complete']}`",
        f"- Invariants passed: `{summary['invariants_passed']}`",
        "",
        "## Equations",
        "",
        f"- `{summary['u1_equation']}`",
        f"- `{summary['v_barrier_equation']}`",
        "",
        "## Rows",
        "",
        "| row_id | layer | status | failure mechanism | consequence |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in rows:
        mechanism = "; ".join(row["failure_mechanism"]).replace("|", "/")
        consequence = row["zero_number_consequence"].replace("|", "/")
        lines.append(
            "| {row_id} | {layer} | {status} | {mechanism} | {consequence} |".format(
                row_id=row["row_id"],
                layer=row["layer"],
                status=row["status"],
                mechanism=mechanism,
                consequence=consequence,
            )
        )
    lines.extend(["", "## Control Card", ""])
    for key, value in summary["control_card"].items():
        lines.append(f"- {key}: {value}")
    lines.extend(
        [
            "",
            "## Governance",
            "",
            "This artifact is fail-closed. It records why sign-changing partial_z^2 psi1, "
            "off-peak source, radial commutators, log Biot-Savart hazards, and the "
            "missing comparison envelope block scalar zero-number transfer.",
            "",
        ]
    )
    path.write_text("\n".join(lines), encoding="utf-8")


def write_artifacts(staging_dir: Path, repo_root: Path, final_out_dir: Path) -> dict[str, Any]:
    rows = build_rows()
    summary = build_summary(rows, read_source_artifact_state(repo_root))
    validate(rows, summary)

    summary_path = staging_dir / SUMMARY_NAME
    rows_json_path = staging_dir / ROWS_JSON_NAME
    rows_csv_path = staging_dir / ROWS_CSV_NAME
    report_path = staging_dir / REPORT_NAME
    manifest_path = staging_dir / MANIFEST_NAME

    write_json(summary_path, summary)
    write_json(rows_json_path, rows)
    write_csv(rows_csv_path, rows)
    write_markdown(report_path, summary, rows)

    manifest = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "files": {
            "summary": display_path(final_out_dir / SUMMARY_NAME, repo_root),
            "rows_json": display_path(final_out_dir / ROWS_JSON_NAME, repo_root),
            "rows_csv": display_path(final_out_dir / ROWS_CSV_NAME, repo_root),
            "markdown": display_path(final_out_dir / REPORT_NAME, repo_root),
            "manifest": display_path(final_out_dir / MANIFEST_NAME, repo_root),
        },
        "sha256": {
            "summary": file_sha256(summary_path),
            "rows_json": file_sha256(rows_json_path),
            "rows_csv": file_sha256(rows_csv_path),
            "markdown": file_sha256(report_path),
        },
        "artifact_complete": summary["artifact_complete"],
        "invariants_passed": summary["invariants_passed"],
    }
    write_json(manifest_path, manifest)
    manifest["sha256"]["manifest"] = file_sha256(manifest_path)
    write_json(manifest_path, manifest)
    return manifest


def emit(repo_root: Path, out_dir: Path) -> dict[str, Any]:
    if not out_dir.is_absolute():
        out_dir = repo_root / out_dir
    out_dir_parent = out_dir.parent
    out_dir_parent.mkdir(parents=True, exist_ok=True)

    with tempfile.TemporaryDirectory(
        prefix=f".{CONTRACT}.", dir=str(out_dir_parent)
    ) as temp_name:
        staging_dir = Path(temp_name)
        manifest = write_artifacts(staging_dir, repo_root, out_dir)
        out_dir.mkdir(parents=True, exist_ok=True)
        for name in (SUMMARY_NAME, ROWS_JSON_NAME, ROWS_CSV_NAME, REPORT_NAME, MANIFEST_NAME):
            os.replace(staging_dir / name, out_dir / name)
    return manifest


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    manifest = emit(repo_root=repo_root, out_dir=args.out_dir)
    print(json.dumps(manifest, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
