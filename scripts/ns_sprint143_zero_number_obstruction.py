#!/usr/bin/env python3
"""Sprint 143 zero-number obstruction ledger emitter.

This deterministic artifact records why scalar one-dimensional Sturm or
zero-number intuition does not directly transfer to the v = partial_z u1
barrier route in the coupled axisymmetric-with-swirl setting.

The decision is intentionally fail-closed.  The ledger does not prove
secondary peak exclusion, does not close the global barrier, and does not emit
any Clay Navier-Stokes promotion.  A closing route would require the missing
theorem CoupledAxisymmetricZeroNumberForVBarrier with constants compatible
with the coupled r-z geometry, nonlocal psi1 feedback, radial transport and
commutator terms, and the moving boundary or annular regimes.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint143_zero_number_obstruction"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint143_zero_number_obstruction")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"
MANIFEST_NAME = CONTRACT + "_manifest.json"

SPRINT = 143
LANE = 4
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
TARGET_GATE = "SecondaryPeakExclusionForVBarrier"
TARGET_VARIABLE = "v = partial_z u1"
MISSING_THEOREM = "CoupledAxisymmetricZeroNumberForVBarrier"
DECISION = "fail_closed_zero_number_transfer_obstructed"

U1_EQUATION = "D_t u1 = 2 u1 partial_z psi1 + nu Ltilde u1"
V_BARRIER_EQUATION = (
    "D_t v = nu Ltilde v + 2 v partial_z psi1 + 2 u1 partial_z^2 psi1 "
    "- (partial_z u^r) partial_r u1 - (partial_z u^z) v"
)

REQUIRED_ROW_IDS = {
    "scalar_sturm_intuition_scope",
    "coupled_rz_geometry_obstruction",
    "nonlocal_psi1_feedback",
    "radial_transport_commutators",
    "moving_boundary_annulus",
    "absent_constants",
    "missing_coupled_zero_number_theorem",
}

SUMMARY_REQUIRED_FALSE = {
    "scalar_zero_number_transfer_valid",
    "coupled_zero_number_theorem_available",
    "secondary_peak_exclusion_proved",
    "global_barrier_closed",
    "full_clay_ns_solved",
    "clay_navier_stokes_promoted",
}


@dataclass(frozen=True)
class ObstructionRow:
    row_id: str
    layer: str
    role: str
    scalar_1d_input: str
    coupled_barrier_feature: str
    obstruction: tuple[str, ...]
    missing_input: tuple[str, ...]
    consequence: str
    scalar_transfer_valid: bool
    theorem_available: bool
    secondary_peak_exclusion_proved: bool
    global_barrier_closed: bool
    clay_navier_stokes_promoted: bool
    status: str

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row["obstruction"] = list(self.obstruction)
        row["missing_input"] = list(self.missing_input)
        row["program"] = PROGRAM
        row["target_gate"] = TARGET_GATE
        row["target_variable"] = TARGET_VARIABLE
        row["missing_theorem"] = MISSING_THEOREM
        row["v_barrier_equation"] = V_BARRIER_EQUATION
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
        return str(path.relative_to(repo_root))
    except ValueError:
        return str(path)


def build_rows() -> list[dict[str, Any]]:
    rows = [
        ObstructionRow(
            row_id="scalar_sturm_intuition_scope",
            layer="scalar_template",
            role="intuition_boundary",
            scalar_1d_input=(
                "A scalar one-dimensional parabolic equation can sometimes "
                "enforce monotone zero-number behavior under suitable regularity "
                "and boundary hypotheses."
            ),
            coupled_barrier_feature=(
                "The v barrier is a differentiated component of a coupled "
                "axisymmetric r-z system rather than a closed scalar 1D equation."
            ),
            obstruction=(
                "v is coupled to u1, psi1, u^r, and u^z",
                "the equation has nonhomogeneous source and transport-gradient terms",
                "the scalar theorem's closed-order structure is absent",
            ),
            missing_input=(MISSING_THEOREM,),
            consequence=(
                "Scalar zero-number intuition is recorded as motivation only; it "
                "cannot be promoted into a transfer theorem for the v barrier."
            ),
            scalar_transfer_valid=False,
            theorem_available=False,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            clay_navier_stokes_promoted=False,
            status="transfer_invalid",
        ),
        ObstructionRow(
            row_id="coupled_rz_geometry_obstruction",
            layer="geometry",
            role="dimension_and_coupling_gap",
            scalar_1d_input=(
                "The scalar zero-number route counts sign changes along a single "
                "spatial variable."
            ),
            coupled_barrier_feature=(
                "The monitored geometry evolves in coupled radial and axial "
                "coordinates with Ltilde = partial_r^2 + 3/r partial_r + partial_z^2."
            ),
            obstruction=(
                "radial derivatives influence the same maximum-principle ledger",
                "axial zeros can move under radial diffusion and radial transport",
                "a fixed z-line count does not control the full r-z first crossing",
            ),
            missing_input=(
                "dimension-reduction theorem for admissible r-z barrier crossings",
                MISSING_THEOREM,
            ),
            consequence=(
                "A one-dimensional sign-change count does not exclude a secondary "
                "positive v maximum in the coupled r-z barrier domain."
            ),
            scalar_transfer_valid=False,
            theorem_available=False,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            clay_navier_stokes_promoted=False,
            status="coupled_geometry_open",
        ),
        ObstructionRow(
            row_id="nonlocal_psi1_feedback",
            layer="elliptic_feedback",
            role="nonlocal_source_gap",
            scalar_1d_input=(
                "Closed scalar equations use coefficients and sources that fit "
                "the hypotheses of the zero-number theorem."
            ),
            coupled_barrier_feature=(
                "The v equation contains 2 u1 partial_z^2 psi1, with psi1 tied "
                "to the global axisymmetric elliptic/Biot-Savart structure."
            ),
            obstruction=(
                "partial_z^2 psi1 is nonlocal and not globally signed",
                "off-peak elliptic feedback can support secondary shoulders",
                "known amplitude controls do not yield zero-count monotonicity",
            ),
            missing_input=(
                "global sign or domination theorem for partial_z^2 psi1",
                MISSING_THEOREM,
            ),
            consequence=(
                "The source term can move or create axial sign changes outside "
                "the scalar zero-number template."
            ),
            scalar_transfer_valid=False,
            theorem_available=False,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            clay_navier_stokes_promoted=False,
            status="nonlocal_feedback_uncontrolled",
        ),
        ObstructionRow(
            row_id="radial_transport_commutators",
            layer="transport_commutator",
            role="sign_indefinite_terms",
            scalar_1d_input=(
                "The scalar route relies on a closed parabolic operator whose "
                "transport and reaction terms preserve the zero-number argument."
            ),
            coupled_barrier_feature=(
                "The differentiated v equation includes radial transport and "
                "the commutator -(partial_z u^r) partial_r u1."
            ),
            obstruction=(
                "partial_r u1 is not fixed by axial first-crossing data",
                "partial_z u^r is coupled nonlocally to the flow",
                "commutator signs can oppose the desired barrier inequality",
            ),
            missing_input=(
                "radial-gradient coupling theorem at first positive v crossings",
                "commutator domination constants compatible with the barrier",
                MISSING_THEOREM,
            ),
            consequence=(
                "Radial transport and commutators prevent a direct Sturmian "
                "transfer from closing secondary peak exclusion."
            ),
            scalar_transfer_valid=False,
            theorem_available=False,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            clay_navier_stokes_promoted=False,
            status="commutator_gap_open",
        ),
        ObstructionRow(
            row_id="moving_boundary_annulus",
            layer="domain_geometry",
            role="boundary_and_annular_hazard",
            scalar_1d_input=(
                "Classical zero-number statements depend on controlled boundary "
                "conditions on a fixed one-dimensional interval."
            ),
            coupled_barrier_feature=(
                "The Hou-Luo route monitors annular, boundary-adjacent, and "
                "possibly moving localization windows in r-z geometry."
            ),
            obstruction=(
                "first crossings may occur near annular or boundary layers",
                "local axial counts do not determine boundary-compatible radial jets",
                "moving localization can shift the relevant comparison interval",
            ),
            missing_input=(
                "boundary-compatible zero-number theorem for the monitored annulus",
                MISSING_THEOREM,
            ),
            consequence=(
                "The scalar fixed-domain zero-count mechanism does not rule out "
                "secondary positive crossings in the annular barrier regime."
            ),
            scalar_transfer_valid=False,
            theorem_available=False,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            clay_navier_stokes_promoted=False,
            status="annular_boundary_gap_open",
        ),
        ObstructionRow(
            row_id="absent_constants",
            layer="quantitative_interface",
            role="constant_compatibility_gap",
            scalar_1d_input=(
                "Even when a qualitative scalar theorem exists, promotion into "
                "a barrier proof requires constants compatible with the route."
            ),
            coupled_barrier_feature=(
                "The global v barrier needs margins for nonlocal psi1 feedback, "
                "radial transport, commutators, and annular boundary terms."
            ),
            obstruction=(
                "no numerical or analytic constants are supplied for the coupled theorem",
                "no domination margin absorbs all source and commutator hazards",
                "no compatibility proof ties zero-number decay to the global barrier",
            ),
            missing_input=(
                "barrier-compatible constants for the missing theorem",
                "global margin ledger for the coupled terms",
                MISSING_THEOREM,
            ),
            consequence=(
                "The ledger cannot close even a conditional quantitative transfer "
                "from scalar zero-number intuition."
            ),
            scalar_transfer_valid=False,
            theorem_available=False,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            clay_navier_stokes_promoted=False,
            status="constants_absent",
        ),
        ObstructionRow(
            row_id="missing_coupled_zero_number_theorem",
            layer="required_theorem_interface",
            role="promotion_blocker",
            scalar_1d_input=(
                "The intended proof would need a valid zero-number theorem for "
                "the actual coupled v-barrier dynamics."
            ),
            coupled_barrier_feature=(
                "The required theorem must cover coupled r-z geometry, nonlocal "
                "psi1, radial transport and commutators, moving boundary or "
                "annular regimes, and explicit constants."
            ),
            obstruction=(
                f"{MISSING_THEOREM} is not supplied",
                "secondary peak exclusion remains unproved",
                "the global barrier remains open",
            ),
            missing_input=(
                MISSING_THEOREM,
                "proof obligations for all row-level obstructions",
                "constants sufficient for promotion into the v barrier route",
            ),
            consequence=(
                "The Sprint 143 ledger remains fail-closed and cannot promote "
                "the Hou-Luo barrier route or Clay Navier-Stokes."
            ),
            scalar_transfer_valid=False,
            theorem_available=False,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            clay_navier_stokes_promoted=False,
            status="required_theorem_missing",
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
        "missing_theorem": MISSING_THEOREM,
        "u1_equation": U1_EQUATION,
        "v_barrier_equation": V_BARRIER_EQUATION,
        "row_count": len(rows),
        "required_row_ids": sorted(REQUIRED_ROW_IDS),
        "observed_row_ids": row_ids,
        "missing_required_row_ids": missing,
        "extra_row_ids": extra,
        "scalar_zero_number_transfer_valid": False,
        "coupled_zero_number_theorem_available": False,
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
                "Worker lane 4 owns only scripts/ns_sprint143_zero_number_obstruction.py "
                "and outputs/ns_sprint143_zero_number_obstruction/."
            ),
            "R": (
                "Record why scalar 1D Sturm/zero-number intuition does not "
                "directly close the coupled v-barrier route."
            ),
            "C": (
                "Deterministic Python emitter producing summary JSON, row JSON, "
                "CSV, Markdown, and a manifest."
            ),
            "S": (
                "All rows keep scalar transfer invalid, the coupled theorem "
                "unavailable, secondary peak exclusion unproved, and the global "
                "barrier open."
            ),
            "L": (
                "Scalar 1D intuition -> coupled r-z and nonlocal feedback gaps "
                "-> commutator, annulus, and constants gaps -> missing theorem."
            ),
            "P": (
                "Use this as an obstruction ledger only; do not treat it as a "
                "zero-number theorem or a barrier closure."
            ),
            "G": (
                "Validation passes only if the fail-closed summary booleans and "
                "row-level proof/promotion flags stay false."
            ),
            "F": (
                f"Missing theorem: {MISSING_THEOREM}; no global barrier closure, "
                "no full Clay Navier-Stokes solution, and no Clay promotion."
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
    if any(row["theorem_available"] for row in rows):
        failures.append("row_theorem_marked_available")
    if any(row["secondary_peak_exclusion_proved"] for row in rows):
        failures.append("row_secondary_peak_exclusion_marked_proved")
    if any(row["global_barrier_closed"] for row in rows):
        failures.append("row_global_barrier_marked_closed")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        failures.append("row_clay_promotion_detected")
    if MISSING_THEOREM not in json.dumps(rows, sort_keys=True):
        failures.append("missing_theorem_not_recorded_in_rows")

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
    if summary["missing_theorem"] != MISSING_THEOREM:
        errors.append("wrong missing theorem")
    if "partial_z^2 psi1" not in summary["v_barrier_equation"]:
        errors.append("v equation must record nonlocal psi1 source")
    if not all(not row["claim_closed"] and not row["claim_proved"] for row in rows):
        errors.append("at least one row incorrectly closes/proves the claim")
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
        f"- Missing theorem: `{summary['missing_theorem']}`",
        (
            "- Scalar zero-number transfer valid: "
            f"`{summary['scalar_zero_number_transfer_valid']}`"
        ),
        (
            "- Coupled zero-number theorem available: "
            f"`{summary['coupled_zero_number_theorem_available']}`"
        ),
        (
            "- Secondary peak exclusion proved: "
            f"`{summary['secondary_peak_exclusion_proved']}`"
        ),
        f"- Global barrier closed: `{summary['global_barrier_closed']}`",
        f"- Full Clay NS solved: `{summary['full_clay_ns_solved']}`",
        f"- Clay promotion: `{summary['clay_navier_stokes_promoted']}`",
        f"- Artifact complete: `{summary['artifact_complete']}`",
        f"- Invariants passed: `{summary['invariants_passed']}`",
        "",
        "## Equations",
        "",
        f"- `{summary['u1_equation']}`",
        f"- `{summary['v_barrier_equation']}`",
        "",
        "## Obstruction Rows",
        "",
        "| row_id | layer | status | obstruction | consequence |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in rows:
        obstruction = "; ".join(row["obstruction"]).replace("|", "/")
        consequence = row["consequence"].replace("|", "/")
        lines.append(
            "| {row_id} | {layer} | {status} | {obstruction} | {consequence} |".format(
                row_id=row["row_id"],
                layer=row["layer"],
                status=row["status"],
                obstruction=obstruction,
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
            "This artifact is fail-closed. It records the missing coupled "
            "zero-number theorem and does not close secondary peak exclusion, "
            "the global barrier, or Clay Navier-Stokes.",
            "",
        ]
    )
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir if args.out_dir.is_absolute() else repo_root / args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    rows = build_rows()
    summary = build_summary(rows)
    validate(rows, summary)

    summary_path = out_dir / SUMMARY_NAME
    rows_json_path = out_dir / ROWS_JSON_NAME
    rows_csv_path = out_dir / ROWS_CSV_NAME
    report_path = out_dir / REPORT_NAME

    write_json(summary_path, summary)
    write_json(rows_json_path, rows)
    write_csv(rows_csv_path, rows)
    write_markdown(report_path, summary, rows)

    manifest = {
        "contract": CONTRACT,
        "files": {
            "summary": display_path(summary_path, repo_root),
            "rows_json": display_path(rows_json_path, repo_root),
            "rows_csv": display_path(rows_csv_path, repo_root),
            "markdown": display_path(report_path, repo_root),
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
    manifest_path = out_dir / MANIFEST_NAME
    write_json(manifest_path, manifest)

    print(json.dumps(manifest, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
