#!/usr/bin/env python3
"""Sprint 141 radial-gradient coupling ledger emitter.

This deterministic artifact records why first axial positive-crossing
conditions for v = partial_z u1 do not, by themselves, control partial_r u1.
The ledger is intentionally fail-closed: the commutator

    -(partial_z u^r) partial_r u1

remains sign-indefinite unless a separate radial-gradient coupling theorem is
supplied.  No global proof and no Clay Navier-Stokes promotion are emitted.
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


CONTRACT = "ns_sprint141_radial_gradient_coupling_ledger"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint141_radial_gradient_coupling_ledger")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"

SPRINT = 141
LANE = 4
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
TARGET_VARIABLE = "v = partial_z u1"
COMMUTATOR = "-(partial_z u^r) partial_r u1"
MISSING_THEOREM = "RadialGradientCouplingAtFirstAxialPositiveCrossing"
DECISION = "fail_closed_missing_radial_gradient_coupling"

REQUIRED_ROW_IDS = {
    "axial_crossing_geometry",
    "radial_slope_freedom",
    "gamma_max_principle_insufficiency",
    "boundary_annulus_hazard",
    "missing_radial_gradient_coupling_theorem",
}


@dataclass(frozen=True)
class CouplingRow:
    row_id: str
    layer: str
    role: str
    crossing_conditions: tuple[str, ...]
    statement: str
    obstruction: str
    radial_gradient_controlled: bool
    commutator_sign_determined: bool
    missing_input: tuple[str, ...]
    consequence: str
    status: str
    global_proof: bool
    clay_navier_stokes_promoted: bool

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row["crossing_conditions"] = list(self.crossing_conditions)
        row["missing_input"] = list(self.missing_input)
        row["target_variable"] = TARGET_VARIABLE
        row["commutator"] = COMMUTATOR
        row["missing_theorem"] = MISSING_THEOREM
        row["partial_r_u1_controlled_by_axial_crossing"] = (
            self.radial_gradient_controlled
        )
        row["claim_closed"] = False
        row["claim_proved"] = False
        row["claim_proven"] = False
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


def build_rows() -> list[dict[str, Any]]:
    rows = [
        CouplingRow(
            row_id="axial_crossing_geometry",
            layer="maximum_principle_geometry",
            role="first_positive_v_crossing",
            crossing_conditions=(
                "v(t*, r*, z*) = 0 at the first attempted positive crossing",
                "partial_r v(t*, r*, z*) = 0 for an interior crossing",
                "partial_z v(t*, r*, z*) = 0 for an interior crossing",
                "Ltilde v(t*, r*, z*) <= 0 at an interior maximum",
            ),
            statement=(
                "The first-crossing geometry constrains v and derivatives of v, "
                "not the independent radial slope partial_r u1."
            ),
            obstruction=(
                "Since partial_r v = partial_r partial_z u1, the condition fixes "
                "a mixed derivative at the crossing but does not determine "
                "partial_r u1 itself."
            ),
            radial_gradient_controlled=False,
            commutator_sign_determined=False,
            missing_input=(
                "identity or theorem linking partial_r u1 to the axial crossing data",
            ),
            consequence=(
                "The commutator sign is not fixed by the standard first-crossing "
                "maximum-principle ledger."
            ),
            status="open_gap",
            global_proof=False,
            clay_navier_stokes_promoted=False,
        ),
        CouplingRow(
            row_id="radial_slope_freedom",
            layer="local_jet_freedom",
            role="radial_gradient_counterledger",
            crossing_conditions=(
                "u1 has the same axial first-crossing jet for v",
                "partial_z u1 vanishes at the crossing point",
                "partial_r partial_z u1 is fixed at the crossing point",
            ),
            statement=(
                "Two local profiles can share the same v-crossing data while "
                "having opposite signs of partial_r u1 at the same point."
            ),
            obstruction=(
                "Adding a radial-only perturbation with zero z-derivative leaves "
                "the v crossing unchanged but changes partial_r u1."
            ),
            radial_gradient_controlled=False,
            commutator_sign_determined=False,
            missing_input=(
                "radial monotonicity or radial-gradient coupling assumption",
                "compatibility with the axisymmetric Biot-Savart/transport system",
            ),
            consequence=(
                "The factor partial_r u1 remains free enough to flip the sign of "
                f"{COMMUTATOR} when partial_z u^r is nonzero."
            ),
            status="open_gap",
            global_proof=False,
            clay_navier_stokes_promoted=False,
        ),
        CouplingRow(
            row_id="gamma_max_principle_insufficiency",
            layer="auxiliary_maximum_principle",
            role="gamma_does_not_close_radial_slope",
            crossing_conditions=(
                "Gamma = r u^theta = r^2 u1 obeys a maximum-principle-type bound",
                "Gamma amplitude control is available along the monitored route",
            ),
            statement=(
                "A maximum principle for Gamma supplies amplitude control but "
                "does not supply pointwise sign control of partial_r u1."
            ),
            obstruction=(
                "Bounds on Gamma or u1 do not prevent steep local radial slopes, "
                "nor do they align partial_r u1 with partial_z u^r at a v crossing."
            ),
            radial_gradient_controlled=False,
            commutator_sign_determined=False,
            missing_input=(
                "gradient estimate strong enough at first v crossings",
                "sign-preserving conversion from Gamma control to partial_r u1 control",
            ),
            consequence=(
                "Gamma control is insufficient to make the commutator favorable "
                "or dominated in the v barrier equation."
            ),
            status="insufficient_input",
            global_proof=False,
            clay_navier_stokes_promoted=False,
        ),
        CouplingRow(
            row_id="boundary_annulus_hazard",
            layer="domain_geometry",
            role="off_axis_and_boundary_hazard",
            crossing_conditions=(
                "first positive crossing may occur away from the axis",
                "annular mass and boundary layers may influence the local velocity gradient",
                "interior axial crossing data do not exhaust boundary-adjacent geometry",
            ),
            statement=(
                "Annular or boundary-adjacent crossings can inherit radial slopes "
                "from domain geometry that are invisible to axial crossing conditions."
            ),
            obstruction=(
                "Boundary and annular contributions can change partial_r u1 or "
                "partial_z u^r without violating the axial first-crossing data for v."
            ),
            radial_gradient_controlled=False,
            commutator_sign_determined=False,
            missing_input=(
                "boundary-compatible radial-gradient estimate",
                "annular exclusion or domination theorem for the commutator",
            ),
            consequence=(
                "The commutator remains a hazard outside any purely axial/local "
                "crossing argument."
            ),
            status="open_hazard",
            global_proof=False,
            clay_navier_stokes_promoted=False,
        ),
        CouplingRow(
            row_id="missing_radial_gradient_coupling_theorem",
            layer="required_theorem_interface",
            role="promotion_blocker",
            crossing_conditions=(
                "all admissible first positive v crossings on the monitored route",
                "including interior, annular, and boundary-compatible cases",
            ),
            statement=(
                "A separate theorem must couple first axial positive-crossing "
                "conditions to partial_r u1 strongly enough to sign or dominate "
                f"{COMMUTATOR}."
            ),
            obstruction=(
                "No such theorem is supplied by this ledger, and the previous "
                "rows show why it is not a formal consequence of axial crossing "
                "geometry or Gamma amplitude control."
            ),
            radial_gradient_controlled=False,
            commutator_sign_determined=False,
            missing_input=(
                MISSING_THEOREM,
                "constants compatible with the v-barrier margin",
                "coverage of annular and boundary crossing regimes",
            ),
            consequence=(
                "The v-barrier route cannot be globally promoted; the commutator "
                "is recorded as sign-indefinite pending the missing theorem."
            ),
            status="required_theorem_missing",
            global_proof=False,
            clay_navier_stokes_promoted=False,
        ),
    ]
    return [row.as_row() for row in rows]


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    row_ids = [row["row_id"] for row in rows]
    missing = sorted(REQUIRED_ROW_IDS.difference(row_ids))
    extra = sorted(set(row_ids).difference(REQUIRED_ROW_IDS))
    sign_indefinite = not any(row["commutator_sign_determined"] for row in rows)
    radial_control_absent = not any(row["radial_gradient_controlled"] for row in rows)

    summary = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "program": PROGRAM,
        "decision": DECISION,
        "target_variable": TARGET_VARIABLE,
        "commutator": COMMUTATOR,
        "missing_theorem": MISSING_THEOREM,
        "row_count": len(rows),
        "required_row_ids": sorted(REQUIRED_ROW_IDS),
        "observed_row_ids": row_ids,
        "missing_required_row_ids": missing,
        "extra_row_ids": extra,
        "radial_gradient_control_absent": radial_control_absent,
        "commutator_sign_indefinite": sign_indefinite,
        "global_proof": False,
        "global_proof_validated_absent": not any(row["global_proof"] for row in rows),
        "clay_navier_stokes_promoted": False,
        "promotion_validated_absent": not any(
            row["clay_navier_stokes_promoted"] for row in rows
        ),
        "claim_closed": False,
        "claim_proved": False,
        "claim_proven": False,
        "validation_passed": False,
    }
    summary["summary_hash"] = stable_hash(
        {k: v for k, v in summary.items() if k != "summary_hash"}
    )
    return summary


def validate(rows: list[dict[str, Any]], summary: dict[str, Any]) -> None:
    errors: list[str] = []
    if summary["missing_required_row_ids"]:
        errors.append(f"missing required rows: {summary['missing_required_row_ids']}")
    if summary["extra_row_ids"]:
        errors.append(f"unexpected rows: {summary['extra_row_ids']}")
    if not summary["radial_gradient_control_absent"]:
        errors.append("radial-gradient control was incorrectly marked present")
    if not summary["commutator_sign_indefinite"]:
        errors.append("commutator was incorrectly marked sign-determined")
    if not summary["global_proof_validated_absent"]:
        errors.append("global proof was incorrectly emitted")
    if not summary["promotion_validated_absent"]:
        errors.append("Clay promotion was incorrectly emitted")
    if any(row["claim_closed"] or row["claim_proved"] or row["claim_proven"] for row in rows):
        errors.append("at least one row incorrectly closes/proves the claim")

    if errors:
        raise ValueError("; ".join(errors))

    summary["validation_passed"] = True
    summary["validation_errors"] = []
    summary["summary_hash"] = stable_hash(
        {k: v for k, v in summary.items() if k != "summary_hash"}
    )


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
        f"- Target: `{TARGET_VARIABLE}`",
        f"- Commutator: `{COMMUTATOR}`",
        f"- Missing theorem: `{MISSING_THEOREM}`",
        f"- Commutator sign-indefinite: `{summary['commutator_sign_indefinite']}`",
        f"- Global proof: `{summary['global_proof']}`",
        f"- Clay promotion: `{summary['clay_navier_stokes_promoted']}`",
        f"- Validation passed: `{summary['validation_passed']}`",
        "",
        "## Rows",
        "",
        "| row_id | role | status | consequence |",
        "| --- | --- | --- | --- |",
    ]
    for row in rows:
        lines.append(
            "| {row_id} | {role} | {status} | {consequence} |".format(
                row_id=row["row_id"],
                role=row["role"],
                status=row["status"],
                consequence=row["consequence"].replace("|", "/"),
            )
        )
    lines.extend(
        [
            "",
            "## Governance",
            "",
            "This ledger is a blocker surface only. It validates absence of a "
            "global proof and absence of promotion; it does not supply the "
            "radial-gradient coupling theorem.",
            "",
        ]
    )
    path.write_text("\n".join(lines), encoding="utf-8")


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
            "summary": str(summary_path.relative_to(repo_root)),
            "rows_json": str(rows_json_path.relative_to(repo_root)),
            "rows_csv": str(rows_csv_path.relative_to(repo_root)),
            "markdown": str(report_path.relative_to(repo_root)),
        },
        "sha256": {
            "summary": file_sha256(summary_path),
            "rows_json": file_sha256(rows_json_path),
            "rows_csv": file_sha256(rows_csv_path),
            "markdown": file_sha256(report_path),
        },
        "validation_passed": summary["validation_passed"],
    }
    manifest_path = out_dir / f"{CONTRACT}_manifest.json"
    write_json(manifest_path, manifest)

    print(json.dumps(manifest, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
