#!/usr/bin/env python3
"""Sprint 144 coupled zero-number theorem-interface ledger emitter.

This deterministic artifact normalizes the theorem interface that would be
needed for CoupledAxisymmetricZeroNumberForVBarrier.  It records the scalar
template, the coupled r-z operator mismatch, nonlocal and commutator gaps,
moving annular boundary hazards, and the constants required before the
v-barrier route could use a zero-number theorem.

The decision is intentionally fail-closed.  This artifact does not prove the
coupled zero-number theorem, does not validate scalar transfer, does not close
secondary peak exclusion, and does not promote Clay Navier-Stokes.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import shutil
import sys
import tempfile
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint144_coupled_zero_number_interface"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint144_coupled_zero_number_interface")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"
MANIFEST_NAME = CONTRACT + "_manifest.json"

SPRINT = 144
LANE = 2
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
TARGET_GATE = "SecondaryPeakExclusionForVBarrier"
TARGET_VARIABLE = "v = partial_z u1"
THEOREM_INTERFACE = "CoupledAxisymmetricZeroNumberForVBarrier"
DECISION = "fail_closed_coupled_zero_number_interface_not_satisfied"

SCALAR_TEMPLATE = (
    "one-dimensional scalar parabolic zero-number theorem on a fixed interval "
    "with closed local operator, admissible boundary data, regular coefficients, "
    "and no sign-indefinite external source capable of creating new zeros"
)
U1_EQUATION = "D_t u1 = 2 u1 partial_z psi1 + nu Ltilde u1"
V_BARRIER_EQUATION = (
    "D_t v = nu Ltilde v + 2 v partial_z psi1 + 2 u1 partial_z^2 psi1 "
    "- (partial_z u^r) partial_r u1 - (partial_z u^z) v"
)
COUPLED_OPERATOR = "Ltilde = partial_r^2 + 3/r partial_r + partial_z^2"

REQUIRED_ROW_IDS = {
    "scalar_template_valid_only_1d",
    "coupled_rz_operator_gap",
    "nonlocal_source_gap",
    "commutator_transport_gap",
    "moving_boundary_annular_gap",
    "constants_compatibility_gap",
    "theorem_absent",
}

SUMMARY_REQUIRED_FALSE = {
    "coupled_zero_number_theorem_proved",
    "scalar_transfer_valid",
    "secondary_peak_exclusion_proved",
    "global_barrier_closed",
    "full_clay_ns_solved",
    "clay_navier_stokes_promoted",
}


@dataclass(frozen=True)
class InterfaceRow:
    row_id: str
    interface_layer: str
    scalar_template_component: str
    coupled_equation_mismatch: str
    hypotheses_needed: tuple[str, ...]
    required_constants: tuple[str, ...]
    obstruction: tuple[str, ...]
    consequence: str
    scalar_transfer_valid: bool
    coupled_zero_number_theorem_proved: bool
    secondary_peak_exclusion_proved: bool
    global_barrier_closed: bool
    clay_navier_stokes_promoted: bool
    status: str

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        for key in (
            "hypotheses_needed",
            "required_constants",
            "obstruction",
        ):
            row[key] = list(row[key])
        row["program"] = PROGRAM
        row["target_gate"] = TARGET_GATE
        row["target_variable"] = TARGET_VARIABLE
        row["theorem_interface"] = THEOREM_INTERFACE
        row["scalar_template"] = SCALAR_TEMPLATE
        row["u1_equation"] = U1_EQUATION
        row["v_barrier_equation"] = V_BARRIER_EQUATION
        row["coupled_operator"] = COUPLED_OPERATOR
        row["claim_closed"] = False
        row["claim_proved"] = False
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
        return str(path.resolve().relative_to(repo_root))
    except ValueError:
        return str(path.resolve())


def resolve_out_dir(repo_root: Path, out_dir: Path) -> Path:
    base = out_dir if out_dir.is_absolute() else repo_root / out_dir
    return base.expanduser().resolve()


def build_rows() -> list[dict[str, Any]]:
    rows = [
        InterfaceRow(
            row_id="scalar_template_valid_only_1d",
            interface_layer="scalar_template",
            scalar_template_component=(
                "Classical zero-number control applies to a scalar one-dimensional "
                "parabolic equation with closed local dynamics on a fixed interval."
            ),
            coupled_equation_mismatch=(
                "The v barrier is a differentiated component of a coupled "
                "axisymmetric r-z system, not a closed scalar 1D equation."
            ),
            hypotheses_needed=(
                "identify an admissible one-dimensional comparison variable",
                "prove the v dynamics restrict to a closed scalar equation on that variable",
                "show all source, transport, and boundary terms satisfy scalar theorem assumptions",
            ),
            required_constants=(
                "coefficient regularity margin for the scalar template",
                "boundary compatibility margin for the comparison interval",
            ),
            obstruction=(
                "scalar theorem input is valid only as a 1D template",
                "no transfer theorem maps that template onto the coupled v barrier",
            ),
            consequence=(
                "The scalar zero-number theorem cannot be used directly for "
                "secondary peak exclusion."
            ),
            scalar_transfer_valid=False,
            coupled_zero_number_theorem_proved=False,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            clay_navier_stokes_promoted=False,
            status="scalar_template_not_transferable",
        ),
        InterfaceRow(
            row_id="coupled_rz_operator_gap",
            interface_layer="coupled_operator",
            scalar_template_component=(
                "The template counts sign changes along one spatial coordinate "
                "under a scalar parabolic operator."
            ),
            coupled_equation_mismatch=(
                f"The v equation uses {COUPLED_OPERATOR}, so radial diffusion "
                "and radial first-crossing geometry interact with axial zeros."
            ),
            hypotheses_needed=(
                "dimension-reduction theorem from r-z crossings to axial zero counts",
                "control of radial jets at every admissible v-barrier crossing",
                "maximum-principle compatibility for the coupled r-z operator",
            ),
            required_constants=(
                "radial diffusion domination margin",
                "axis/annulus regularity constants for 3/r partial_r",
                "r-z localization constants compatible with the barrier scale",
            ),
            obstruction=(
                "a fixed z-line zero count does not control the full r-z operator",
                "radial terms can move the first crossing outside scalar theorem scope",
            ),
            consequence=(
                "The coupled operator gap leaves the theorem interface open."
            ),
            scalar_transfer_valid=False,
            coupled_zero_number_theorem_proved=False,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            clay_navier_stokes_promoted=False,
            status="coupled_rz_operator_unmatched",
        ),
        InterfaceRow(
            row_id="nonlocal_source_gap",
            interface_layer="nonlocal_source",
            scalar_template_component=(
                "The scalar template requires source terms that preserve or fit "
                "the zero-number monotonicity hypotheses."
            ),
            coupled_equation_mismatch=(
                "The v equation contains 2 u1 partial_z^2 psi1, where psi1 is "
                "determined by the global elliptic/Biot-Savart structure."
            ),
            hypotheses_needed=(
                "sign or domination theorem for partial_z^2 psi1 in the barrier region",
                "nonlocal feedback bound that cannot create secondary positive peaks",
                "compatibility between elliptic estimates and zero-number decay",
            ),
            required_constants=(
                "global psi1 second-axial-derivative bound",
                "u1-weighted nonlocal source absorption margin",
                "off-peak shoulder suppression constant",
            ),
            obstruction=(
                "partial_z^2 psi1 is nonlocal and not globally signed",
                "known bounds do not prevent source-driven zero creation",
            ),
            consequence=(
                "The nonlocal source term blocks scalar zero-number transfer."
            ),
            scalar_transfer_valid=False,
            coupled_zero_number_theorem_proved=False,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            clay_navier_stokes_promoted=False,
            status="nonlocal_source_uncontrolled",
        ),
        InterfaceRow(
            row_id="commutator_transport_gap",
            interface_layer="transport_commutator",
            scalar_template_component=(
                "The scalar template needs transport and reaction coefficients "
                "that do not introduce sign-indefinite forcing outside the theorem."
            ),
            coupled_equation_mismatch=(
                "The differentiated equation includes -(partial_z u^r) partial_r u1 "
                "and -(partial_z u^z) v in addition to transported diffusion."
            ),
            hypotheses_needed=(
                "radial-gradient coupling control for partial_r u1",
                "nonlocal velocity-gradient bounds for partial_z u^r and partial_z u^z",
                "commutator domination inequality at first positive v crossings",
            ),
            required_constants=(
                "partial_z u^r times partial_r u1 absorption constant",
                "velocity-gradient reaction bound",
                "transport commutator margin compatible with the global barrier",
            ),
            obstruction=(
                "commutator signs are not fixed by axial zero-count data",
                "transport-gradient terms can oppose the desired barrier inequality",
            ),
            consequence=(
                "The theorem interface cannot close without commutator transport constants."
            ),
            scalar_transfer_valid=False,
            coupled_zero_number_theorem_proved=False,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            clay_navier_stokes_promoted=False,
            status="commutator_transport_open",
        ),
        InterfaceRow(
            row_id="moving_boundary_annular_gap",
            interface_layer="domain_geometry",
            scalar_template_component=(
                "The scalar template assumes a fixed interval with boundary "
                "conditions compatible with zero-number monotonicity."
            ),
            coupled_equation_mismatch=(
                "The v barrier is monitored in annular and boundary-adjacent "
                "r-z regions whose localization may move with the route."
            ),
            hypotheses_needed=(
                "zero-number theorem on moving annular comparison domains",
                "boundary jet compatibility for the axisymmetric r-z barrier",
                "proof that localization changes do not reset or hide zero counts",
            ),
            required_constants=(
                "annular boundary trace constant",
                "moving-window speed and curvature margin",
                "boundary layer absorption constant",
            ),
            obstruction=(
                "fixed-interval scalar hypotheses do not cover annular moving windows",
                "boundary-adjacent crossings can depend on radial jets not counted axially",
            ),
            consequence=(
                "Moving boundary and annular regimes remain outside the normalized interface."
            ),
            scalar_transfer_valid=False,
            coupled_zero_number_theorem_proved=False,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            clay_navier_stokes_promoted=False,
            status="moving_annular_domain_open",
        ),
        InterfaceRow(
            row_id="constants_compatibility_gap",
            interface_layer="quantitative_constants",
            scalar_template_component=(
                "A usable theorem interface must expose constants that compose "
                "with the surrounding barrier and domination ledgers."
            ),
            coupled_equation_mismatch=(
                "The coupled theorem would need simultaneous margins for r-z "
                "operator terms, nonlocal psi1 forcing, commutators, transport, "
                "and moving annular boundaries."
            ),
            hypotheses_needed=(
                "single constants ledger spanning all theorem assumptions",
                "monotone implication from theorem constants to secondary peak exclusion",
                "compatibility proof with existing global barrier constants",
            ),
            required_constants=(
                "operator gap constant",
                "nonlocal source constant",
                "commutator transport constant",
                "moving annular boundary constant",
                "global barrier closure margin",
            ),
            obstruction=(
                "no compatible constants are supplied",
                "qualitative scalar intuition is insufficient for promotion",
            ),
            consequence=(
                "The interface cannot be consumed by the global v-barrier route."
            ),
            scalar_transfer_valid=False,
            coupled_zero_number_theorem_proved=False,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            clay_navier_stokes_promoted=False,
            status="constants_not_compatible",
        ),
        InterfaceRow(
            row_id="theorem_absent",
            interface_layer="required_theorem",
            scalar_template_component=(
                "The intended route would require a proved theorem matching the "
                "actual coupled v-barrier dynamics."
            ),
            coupled_equation_mismatch=(
                f"{THEOREM_INTERFACE} is not present with hypotheses and "
                "constants covering every normalized interface gap."
            ),
            hypotheses_needed=(
                THEOREM_INTERFACE,
                "proof that scalar transfer is valid for the coupled v equation",
                "proof that the theorem excludes secondary positive v peaks",
                "proof that the resulting exclusion closes the global barrier",
            ),
            required_constants=(
                "complete theorem constants tuple",
                "constants compatibility certificate",
                "promotion-safe global barrier margin",
            ),
            obstruction=(
                f"{THEOREM_INTERFACE} is absent",
                "secondary peak exclusion remains unproved",
                "the global barrier remains open",
            ),
            consequence=(
                "The artifact stays fail-closed with no Clay Navier-Stokes promotion."
            ),
            scalar_transfer_valid=False,
            coupled_zero_number_theorem_proved=False,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            clay_navier_stokes_promoted=False,
            status="required_theorem_absent",
        ),
    ]
    return [row.as_row() for row in rows]


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    row_ids = [row["row_id"] for row in rows]
    missing = sorted(REQUIRED_ROW_IDS.difference(row_ids))
    extra = sorted(set(row_ids).difference(REQUIRED_ROW_IDS))

    summary = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "program": PROGRAM,
        "decision": DECISION,
        "target_gate": TARGET_GATE,
        "target_variable": TARGET_VARIABLE,
        "theorem_interface": THEOREM_INTERFACE,
        "scalar_template": SCALAR_TEMPLATE,
        "u1_equation": U1_EQUATION,
        "v_barrier_equation": V_BARRIER_EQUATION,
        "coupled_operator": COUPLED_OPERATOR,
        "row_count": len(rows),
        "required_row_ids": sorted(REQUIRED_ROW_IDS),
        "observed_row_ids": row_ids,
        "missing_required_row_ids": missing,
        "extra_row_ids": extra,
        "coupled_zero_number_theorem_proved": False,
        "scalar_transfer_valid": False,
        "secondary_peak_exclusion_proved": False,
        "global_barrier_closed": False,
        "global_proof": False,
        "global_proof_closed": False,
        "no_global_proof": True,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "no_promotion": True,
        "artifact_complete": False,
        "invariants_passed": False,
        "invariant_failures": [],
        "control_card": {
            "O": (
                "Worker lane 2 owns only scripts/ns_sprint144_coupled_zero_number_interface.py "
                "and outputs/ns_sprint144_coupled_zero_number_interface/."
            ),
            "R": (
                "Normalize the missing theorem interface for "
                "CoupledAxisymmetricZeroNumberForVBarrier."
            ),
            "C": (
                "Deterministic Python emitter producing summary JSON, row JSON, "
                "CSV, Markdown, and a manifest through a temporary output directory."
            ),
            "S": (
                "All rows keep the coupled theorem unproved, scalar transfer invalid, "
                "secondary peak exclusion unproved, and the global barrier open."
            ),
            "L": (
                "Scalar 1D template -> coupled r-z operator gap -> nonlocal source "
                "gap -> commutator transport gap -> moving annular gap -> constants "
                "gap -> absent theorem."
            ),
            "P": (
                "Use this as an interface ledger only; do not treat it as a theorem, "
                "secondary peak exclusion proof, barrier closure, or Clay promotion."
            ),
            "G": (
                "Validation passes only if required rows are exact and all proof, "
                "transfer, closure, and promotion booleans stay false."
            ),
            "F": (
                f"Missing theorem interface: {THEOREM_INTERFACE}; no scalar transfer, "
                "no secondary peak exclusion, no global barrier closure, no full Clay "
                "Navier-Stokes solution, and no Clay promotion."
            ),
        },
    }

    failures: list[str] = []
    if missing:
        failures.append("missing_required_rows:" + ",".join(missing))
    if extra:
        failures.append("unexpected_rows:" + ",".join(extra))
    if any(row["scalar_transfer_valid"] for row in rows):
        failures.append("row_scalar_transfer_marked_valid")
    if any(row["coupled_zero_number_theorem_proved"] for row in rows):
        failures.append("row_coupled_theorem_marked_proved")
    if any(row["secondary_peak_exclusion_proved"] for row in rows):
        failures.append("row_secondary_peak_exclusion_marked_proved")
    if any(row["global_barrier_closed"] for row in rows):
        failures.append("row_global_barrier_marked_closed")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        failures.append("row_clay_promotion_detected")
    encoded_rows = json.dumps(rows, sort_keys=True)
    for needle in (
        THEOREM_INTERFACE,
        "hypotheses_needed",
        "required_constants",
        "partial_z^2 psi1",
        "partial_r u1",
    ):
        if needle not in encoded_rows:
            failures.append(f"missing_interface_needle:{needle}")

    summary["invariant_failures"] = failures
    summary["invariants_passed"] = not failures
    summary["invariant_checked"] = summary["invariants_passed"]
    summary["invariant_valid"] = summary["invariants_passed"]
    summary["artifact_complete"] = summary["invariants_passed"]
    summary["summary_hash"] = stable_hash(
        {k: v for k, v in summary.items() if k != "summary_hash"}
    )
    return summary


def validate(rows: list[dict[str, Any]], summary: dict[str, Any]) -> None:
    errors: list[str] = []
    for key in SUMMARY_REQUIRED_FALSE:
        if summary[key]:
            errors.append(f"{key} must remain false")
    if not summary["artifact_complete"]:
        errors.append("artifact_complete must be true after invariant validation")
    if not summary["invariants_passed"]:
        errors.append("invariants_passed must be true")
    if summary["missing_required_row_ids"]:
        errors.append(f"missing required rows: {summary['missing_required_row_ids']}")
    if summary["extra_row_ids"]:
        errors.append(f"unexpected rows: {summary['extra_row_ids']}")
    if summary["theorem_interface"] != THEOREM_INTERFACE:
        errors.append("wrong theorem interface")
    if summary["observed_row_ids"] != [
        "scalar_template_valid_only_1d",
        "coupled_rz_operator_gap",
        "nonlocal_source_gap",
        "commutator_transport_gap",
        "moving_boundary_annular_gap",
        "constants_compatibility_gap",
        "theorem_absent",
    ]:
        errors.append("row order changed")
    if "partial_z^2 psi1" not in summary["v_barrier_equation"]:
        errors.append("v equation must record nonlocal psi1 source")
    if not all(not row["claim_closed"] and not row["claim_proved"] for row in rows):
        errors.append("at least one row incorrectly closes/proves the claim")
    if not all(row["hypotheses_needed"] and row["required_constants"] for row in rows):
        errors.append("every row must record hypotheses_needed and required_constants")
    if summary["invariant_failures"]:
        errors.extend(summary["invariant_failures"])

    if errors:
        raise ValueError("; ".join(errors))


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = list(rows[0].keys())
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow(
                {
                    key: json.dumps(value, sort_keys=True)
                    if isinstance(value, list)
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
        f"- Theorem interface: `{summary['theorem_interface']}`",
        f"- Coupled zero-number theorem proved: `{summary['coupled_zero_number_theorem_proved']}`",
        f"- Scalar transfer valid: `{summary['scalar_transfer_valid']}`",
        f"- Secondary peak exclusion proved: `{summary['secondary_peak_exclusion_proved']}`",
        f"- Global barrier closed: `{summary['global_barrier_closed']}`",
        f"- Full Clay NS solved: `{summary['full_clay_ns_solved']}`",
        f"- Clay promotion: `{summary['clay_navier_stokes_promoted']}`",
        f"- Artifact complete: `{summary['artifact_complete']}`",
        f"- Invariants passed: `{summary['invariants_passed']}`",
        "",
        "## Interface",
        "",
        f"- Scalar template: {summary['scalar_template']}",
        f"- Coupled operator: `{summary['coupled_operator']}`",
        f"- u1 equation: `{summary['u1_equation']}`",
        f"- v equation: `{summary['v_barrier_equation']}`",
        "",
        "## Normalized Rows",
        "",
        "| row_id | layer | status | hypotheses needed | required constants | consequence |",
        "| --- | --- | --- | --- | --- | --- |",
    ]
    for row in rows:
        hypotheses = "; ".join(row["hypotheses_needed"]).replace("|", "/")
        constants = "; ".join(row["required_constants"]).replace("|", "/")
        consequence = row["consequence"].replace("|", "/")
        lines.append(
            "| {row_id} | {layer} | {status} | {hypotheses} | {constants} | {consequence} |".format(
                row_id=row["row_id"],
                layer=row["interface_layer"],
                status=row["status"],
                hypotheses=hypotheses,
                constants=constants,
                consequence=consequence,
            )
        )
    lines.extend(
        [
            "",
            "## Control Card",
            "",
        ]
    )
    for key, value in summary["control_card"].items():
        lines.append(f"- {key}: {value}")
    lines.extend(
        [
            "",
            "## Governance",
            "",
            "This artifact is fail-closed. It normalizes the missing coupled "
            "zero-number theorem interface and does not close scalar transfer, "
            "secondary peak exclusion, the global barrier, or Clay Navier-Stokes.",
            "",
        ]
    )
    path.write_text("\n".join(lines), encoding="utf-8")


def publish_files(temp_dir: Path, out_dir: Path, filenames: tuple[str, ...]) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    for filename in filenames:
        shutil.move(str(temp_dir / filename), str(out_dir / filename))


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.expanduser().resolve()
    out_dir = resolve_out_dir(repo_root, args.out_dir)
    out_parent = out_dir.parent
    out_parent.mkdir(parents=True, exist_ok=True)

    rows = build_rows()
    summary = build_summary(rows)
    validate(rows, summary)

    filenames = (
        SUMMARY_NAME,
        ROWS_JSON_NAME,
        ROWS_CSV_NAME,
        REPORT_NAME,
        MANIFEST_NAME,
    )

    with tempfile.TemporaryDirectory(
        prefix=f".{CONTRACT}.", dir=str(out_parent)
    ) as temp_name:
        temp_dir = Path(temp_name)
        summary_path = temp_dir / SUMMARY_NAME
        rows_json_path = temp_dir / ROWS_JSON_NAME
        rows_csv_path = temp_dir / ROWS_CSV_NAME
        report_path = temp_dir / REPORT_NAME

        write_json(summary_path, summary)
        write_json(rows_json_path, rows)
        write_csv(rows_csv_path, rows)
        write_markdown(report_path, summary, rows)

        manifest = {
            "contract": CONTRACT,
            "files": {
                "summary": display_path(out_dir / SUMMARY_NAME, repo_root),
                "rows_json": display_path(out_dir / ROWS_JSON_NAME, repo_root),
                "rows_csv": display_path(out_dir / ROWS_CSV_NAME, repo_root),
                "markdown": display_path(out_dir / REPORT_NAME, repo_root),
            },
            "sha256": {
                "summary": file_sha256(summary_path),
                "rows_json": file_sha256(rows_json_path),
                "rows_csv": file_sha256(rows_csv_path),
                "markdown": file_sha256(report_path),
            },
            "artifact_complete": summary["artifact_complete"],
            "invariants_passed": summary["invariants_passed"],
            "temp_publish_strategy": "sibling_temp_dir_then_move",
        }
        manifest_path = temp_dir / MANIFEST_NAME
        write_json(manifest_path, manifest)

        publish_files(temp_dir, out_dir, filenames)

    print(json.dumps(manifest, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
