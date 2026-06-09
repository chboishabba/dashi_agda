#!/usr/bin/env python3
"""Sprint 143 secondary peak exclusion ledger emitter.

This deterministic ledger normalizes the theorem still needed to close the
secondary-peak blocker:

    no secondary axial peak/shoulder/off-route positive local maximum of
    v = partial_z u1 on the monitored interval.

The artifact is intentionally fail-closed.  It records the supporting inputs,
the failure modes that remain open, and the missing theorem/constants without
claiming a global barrier, a global Navier-Stokes proof, or Clay promotion.
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


CONTRACT = "ns_sprint143_secondary_peak_exclusion_ledger"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint143_secondary_peak_exclusion_ledger")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"

SPRINT = 143
LANE = 2
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
PARENT_GATE = "AxialMonotonicityOfSwirlProfile"
BLOCKER = "SecondaryPeakExclusion"
NORMALIZED_THEOREM_NEEDED = (
    "No secondary axial peak, shoulder, or off-route positive local maximum "
    "of v=partial_z u1 forms on the monitored interval."
)
MONITORED_VARIABLE = "v = partial_z u1"
MONITORED_INTERVAL = "barrier-monitoring interval shared by the axial monotonicity route"
DECISION = "fail_closed_secondary_peak_exclusion_ledger_open"
PROMOTION_DECISION = "hold_no_clay_promotion"

V_BARRIER_EQUATION = (
    "D_t v = nu Ltilde v + 2 v partial_z psi1 + 2 u1 partial_z^2 psi1 "
    "- (partial_z u^r) partial_r u1 - (partial_z u^z) v"
)

INITIAL_SINGLE_PEAK_SUPPORT = "initial_single_peak_support"
SYMMETRY_SUPPORT = "symmetry_support"
PARABOLIC_SMOOTHING_INSUFFICIENCY = "parabolic_smoothing_insufficiency"
NONLINEAR_SOURCE_SHOULDER = "nonlinear_source_shoulder"
BOUNDARY_ANNULAR_MIGRATION = "boundary_annular_migration"
MISSING_COUPLED_ZERO_NUMBER_THEOREM = "missing_coupled_zero_number_theorem"
MISSING_CONSTANTS = "missing_constants"

REQUIRED_ROW_IDS = {
    INITIAL_SINGLE_PEAK_SUPPORT,
    SYMMETRY_SUPPORT,
    PARABOLIC_SMOOTHING_INSUFFICIENCY,
    NONLINEAR_SOURCE_SHOULDER,
    BOUNDARY_ANNULAR_MIGRATION,
    MISSING_COUPLED_ZERO_NUMBER_THEOREM,
    MISSING_CONSTANTS,
}

SOURCE_ARTIFACTS = {
    "sprint138_secondary_peak": "outputs/ns_sprint138_secondary_peak_exclusion/ns_sprint138_secondary_peak_exclusion_summary.json",
    "sprint140_constant_compatibility": "outputs/ns_sprint140_constant_compatibility_ledger/ns_sprint140_constant_compatibility_ledger_summary.json",
    "sprint142_boundary_annulus_concavity": "outputs/ns_sprint142_boundary_annulus_concavity_ledger/ns_sprint142_boundary_annulus_concavity_ledger_summary.json",
}


@dataclass(frozen=True)
class SecondaryPeakLedgerRow:
    row_id: str
    ledger_role: str
    status: str
    normalized_claim_fragment: str
    support_available: tuple[str, ...]
    obstruction: tuple[str, ...]
    required_input: tuple[str, ...]
    barrier_consequence: str
    theorem_fragment_closed: bool
    secondary_peak_exclusion_proved: bool
    secondary_peak_exclusion_closed: bool
    global_barrier_closed: bool
    global_proof: bool
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool
    promotion_allowed: bool

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        for key in ("support_available", "obstruction", "required_input"):
            row[key] = list(row[key])
        row["program"] = PROGRAM
        row["parent_gate"] = PARENT_GATE
        row["blocker"] = BLOCKER
        row["monitored_variable"] = MONITORED_VARIABLE
        row["monitored_interval"] = MONITORED_INTERVAL
        row["normalized_theorem_needed"] = NORMALIZED_THEOREM_NEEDED
        row["v_barrier_equation"] = V_BARRIER_EQUATION
        row["claim_closed"] = self.secondary_peak_exclusion_closed
        row["claim_proved"] = self.secondary_peak_exclusion_proved
        row["claim_proven"] = self.secondary_peak_exclusion_proved
        row["promotion_decision"] = PROMOTION_DECISION
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
        SecondaryPeakLedgerRow(
            row_id=INITIAL_SINGLE_PEAK_SUPPORT,
            ledger_role="initial_shape_support",
            status="support_recorded_not_persistent",
            normalized_claim_fragment=(
                "The monitored half-profile may begin with one primary axial "
                "peak and no off-route positive local maximum of v."
            ),
            support_available=(
                "Sprint 138 single-peak initial profile row",
                "smooth classical initial data",
                "initial sign pattern v<=0 away from the symmetry-center peak",
            ),
            obstruction=(
                "initial single-peak shape is not a propagated invariant",
                "the v equation is coupled and nonhomogeneous rather than scalar heat flow",
                "no time-persistence theorem keeps the first crossing on the primary route",
            ),
            required_input=(
                "single-peak persistence theorem over the monitored interval",
                "proof that all first positive v maxima remain on the primary axial route",
            ),
            barrier_consequence=(
                "Initial support can start the barrier argument but cannot close "
                "secondary peak exclusion."
            ),
            theorem_fragment_closed=False,
            secondary_peak_exclusion_proved=False,
            secondary_peak_exclusion_closed=False,
            global_barrier_closed=False,
            global_proof=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        SecondaryPeakLedgerRow(
            row_id=SYMMETRY_SUPPORT,
            ledger_role="symmetry_axis_support",
            status="support_recorded_local_only",
            normalized_claim_fragment=(
                "Symmetry identifies the primary axial route and can force "
                "structured behavior at the center plane."
            ),
            support_available=(
                "Hou-Luo symmetric branch bookkeeping",
                "center-plane parity constraints",
                "primary local barrier region from earlier axial monotonicity ledgers",
            ),
            obstruction=(
                "symmetry at the primary center does not order the full monitored interval",
                "symmetric pairs of off-center shoulders are still compatible with parity",
                "off-route local maxima can appear without violating center-plane symmetry",
            ),
            required_input=(
                "symmetry-to-global-unimodality theorem",
                "proof excluding symmetric off-center shoulder pairs for v",
            ),
            barrier_consequence=(
                "Symmetry helps locate the intended route but does not exclude "
                "secondary axial shoulders."
            ),
            theorem_fragment_closed=False,
            secondary_peak_exclusion_proved=False,
            secondary_peak_exclusion_closed=False,
            global_barrier_closed=False,
            global_proof=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        SecondaryPeakLedgerRow(
            row_id=PARABOLIC_SMOOTHING_INSUFFICIENCY,
            ledger_role="regularization_limit",
            status="support_insufficient",
            normalized_claim_fragment=(
                "Parabolic smoothing controls regularity but is insufficient to "
                "prove no new positive local maximum of v forms off route."
            ),
            support_available=(
                "viscous term nu Ltilde v",
                "classical smoothing for positive viscosity",
                "nonpositive diffusion sign at an interior positive maximum",
            ),
            obstruction=(
                "smoothing does not preserve unimodality in the coupled equation",
                "source and transport-gradient terms can offset diffusion",
                "boundary and annular localization can move the relevant maximum",
            ),
            required_input=(
                "comparison principle adapted to the full v equation",
                "strict residual inequality after source, transport, boundary, and annular terms",
            ),
            barrier_consequence=(
                "Diffusion alone cannot be used as the secondary-peak exclusion theorem."
            ),
            theorem_fragment_closed=False,
            secondary_peak_exclusion_proved=False,
            secondary_peak_exclusion_closed=False,
            global_barrier_closed=False,
            global_proof=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        SecondaryPeakLedgerRow(
            row_id=NONLINEAR_SOURCE_SHOULDER,
            ledger_role="nonlinear_shoulder_failure_mode",
            status="open_failure_mode",
            normalized_claim_fragment=(
                "The nonlinear source can raise an off-route shoulder of v "
                "before the primary local barrier yields a contradiction."
            ),
            support_available=(
                V_BARRIER_EQUATION,
                "Sprint 138 nonlinear shoulder row",
                "Sprint 140 constant ledger requires a secondary exclusion radius/window",
            ),
            obstruction=(
                "2 u1 partial_z^2 psi1 is not globally signed on the monitored interval",
                "transport-gradient terms can reinforce off-route growth",
                "local concavity support does not cover every possible first positive maximum",
            ),
            required_input=(
                "global sign, domination, or cancellation theorem for the active nonlinear source",
                "proof that nonlinear forcing cannot create a secondary shoulder of v",
            ),
            barrier_consequence=(
                "A shoulder can become the first positive local maximum outside "
                "the controlled primary patch."
            ),
            theorem_fragment_closed=False,
            secondary_peak_exclusion_proved=False,
            secondary_peak_exclusion_closed=False,
            global_barrier_closed=False,
            global_proof=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        SecondaryPeakLedgerRow(
            row_id=BOUNDARY_ANNULAR_MIGRATION,
            ledger_role="off_route_migration_failure_mode",
            status="open_boundary_annular_hazard",
            normalized_claim_fragment=(
                "A candidate positive maximum can migrate toward boundary or "
                "annular regions not covered by the primary axial route."
            ),
            support_available=(
                "Sprint 142 boundary/annulus concavity ledger",
                "annular Hou-Luo scaling window",
                "Gamma maximum-principle amplitude support",
            ),
            obstruction=(
                "Gamma amplitude control does not control axial zero counts of v",
                "boundary-compatible elliptic effects can change the active source sign",
                "annular shoulders can sit outside the local primary route",
            ),
            required_input=(
                "boundary-compatible secondary-peak exclusion theorem",
                "annular migration exclusion or signed-kernel domination theorem",
                "proof that the monitored interval stays inside one common barrier window",
            ),
            barrier_consequence=(
                "The first positive v maximum may occur where the global barrier "
                "constants are unavailable."
            ),
            theorem_fragment_closed=False,
            secondary_peak_exclusion_proved=False,
            secondary_peak_exclusion_closed=False,
            global_barrier_closed=False,
            global_proof=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        SecondaryPeakLedgerRow(
            row_id=MISSING_COUPLED_ZERO_NUMBER_THEOREM,
            ledger_role="zero_number_gap",
            status="missing_theorem",
            normalized_claim_fragment=(
                "No coupled zero-number theorem is available to prevent creation "
                "of new zeros or positive local maxima of v."
            ),
            support_available=(
                "scalar one-dimensional parabolic zero-number theory is a known template",
                "v is the axial derivative of u1",
            ),
            obstruction=(
                "the equation is axisymmetric in (r,z) and coupled through psi1",
                "nonlocal elliptic feedback is outside scalar Sturmian theory",
                "source terms can create or move zeros of v",
            ),
            required_input=(
                "coupled axisymmetric zero-number or shape-persistence theorem",
                "formal bridge from that theorem to no secondary positive local maximum of v",
            ),
            barrier_consequence=(
                "The ledger cannot infer preservation of the initial sign-change "
                "pattern on the monitored interval."
            ),
            theorem_fragment_closed=False,
            secondary_peak_exclusion_proved=False,
            secondary_peak_exclusion_closed=False,
            global_barrier_closed=False,
            global_proof=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        SecondaryPeakLedgerRow(
            row_id=MISSING_CONSTANTS,
            ledger_role="constant_gap",
            status="missing_constants",
            normalized_claim_fragment=(
                "Even a conditional exclusion route needs explicit compatible "
                "constants for radius, time window, source dominance, and margins."
            ),
            support_available=(
                "Sprint 140 constant compatibility ledger names the required windows",
                "secondary-peak exclusion radius/window is an explicit assembly input",
            ),
            obstruction=(
                "no scale-uniform exclusion radius is supplied",
                "no monitored time window is matched to concavity and commutator constants",
                "no strict combined inequality closes all source, diffusion, strain, boundary, and annular terms",
            ),
            required_input=(
                "R_excl and T_excl for the monitored interval",
                "quantitative margin budget compatible with all barrier ledgers",
                "source, boundary, annular, diffusion, strain, and commutator constants on one crossing set",
            ),
            barrier_consequence=(
                "The normalized theorem remains an obligation rather than a "
                "usable barrier input."
            ),
            theorem_fragment_closed=False,
            secondary_peak_exclusion_proved=False,
            secondary_peak_exclusion_closed=False,
            global_barrier_closed=False,
            global_proof=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
    ]
    materialized = [row.as_row() for row in rows]
    validate_rows(materialized)
    return materialized


def validate_rows(rows: list[dict[str, Any]]) -> None:
    row_ids = {row["row_id"] for row in rows}
    if row_ids != REQUIRED_ROW_IDS:
        missing = sorted(REQUIRED_ROW_IDS - row_ids)
        extra = sorted(row_ids - REQUIRED_ROW_IDS)
        raise ValueError(f"row-id mismatch: missing={missing} extra={extra}")
    for row in rows:
        if row["theorem_fragment_closed"]:
            raise ValueError(f"{row['row_id']} incorrectly closes a theorem fragment")
        for forbidden in (
            "secondary_peak_exclusion_proved",
            "secondary_peak_exclusion_closed",
            "global_barrier_closed",
            "global_proof",
            "full_clay_ns_solved",
            "clay_navier_stokes_promoted",
            "promotion_allowed",
            "claim_closed",
            "claim_proved",
            "claim_proven",
        ):
            if row[forbidden]:
                raise ValueError(f"{row['row_id']} has forbidden true flag: {forbidden}")
        if not row["required_input"]:
            raise ValueError(f"{row['row_id']} has no required inputs")


def build_summary(repo_root: Path, rows: list[dict[str, Any]]) -> dict[str, Any]:
    row_by_id = {row["row_id"]: row for row in rows}
    row_hashes = {row["row_id"]: row["row_hash"] for row in rows}
    rows_hash = stable_hash(rows)
    source_hashes = {
        key: file_sha256(repo_root / relative_path)
        for key, relative_path in SOURCE_ARTIFACTS.items()
    }

    invariant_failures: list[str] = []
    if set(row_by_id) != REQUIRED_ROW_IDS:
        invariant_failures.append("required_rows_mismatch")
    if any(row["secondary_peak_exclusion_proved"] for row in rows):
        invariant_failures.append("secondary_peak_exclusion_proved_detected")
    if any(row["secondary_peak_exclusion_closed"] for row in rows):
        invariant_failures.append("secondary_peak_exclusion_closed_detected")
    if any(row["global_barrier_closed"] for row in rows):
        invariant_failures.append("global_barrier_closed_detected")
    if any(row["global_proof"] for row in rows):
        invariant_failures.append("global_proof_detected")
    if any(row["full_clay_ns_solved"] for row in rows):
        invariant_failures.append("full_clay_ns_solved_detected")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        invariant_failures.append("clay_promotion_detected")
    if any(row["promotion_allowed"] for row in rows):
        invariant_failures.append("promotion_allowed_detected")
    if "secondary axial peak" not in NORMALIZED_THEOREM_NEEDED:
        invariant_failures.append("normalized_theorem_missing_secondary_peak")
    if "off-route positive local maximum" not in NORMALIZED_THEOREM_NEEDED:
        invariant_failures.append("normalized_theorem_missing_off_route_maximum")
    if "v=partial_z u1" not in NORMALIZED_THEOREM_NEEDED:
        invariant_failures.append("normalized_theorem_missing_v")
    if row_by_id[MISSING_CONSTANTS]["status"] != "missing_constants":
        invariant_failures.append("missing_constants_row_not_marked")

    invariants_passed = not invariant_failures

    return {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "program": PROGRAM,
        "parent_gate": PARENT_GATE,
        "blocker": BLOCKER,
        "decision": DECISION,
        "promotion_decision": PROMOTION_DECISION,
        "normalized_theorem_needed": NORMALIZED_THEOREM_NEEDED,
        "monitored_variable": MONITORED_VARIABLE,
        "monitored_interval": MONITORED_INTERVAL,
        "v_barrier_equation": V_BARRIER_EQUATION,
        "row_count": len(rows),
        "required_row_ids": sorted(REQUIRED_ROW_IDS),
        "open_row_ids": sorted(row_by_id),
        "source_artifacts": SOURCE_ARTIFACTS,
        "source_summary_hashes": source_hashes,
        "row_hashes": row_hashes,
        "rows_hash": rows_hash,
        "summary_payload_hash_without_self": stable_hash(
            {
                "contract": CONTRACT,
                "normalized_theorem_needed": NORMALIZED_THEOREM_NEEDED,
                "required_row_ids": sorted(REQUIRED_ROW_IDS),
                "row_hashes": row_hashes,
                "rows_hash": rows_hash,
            }
        ),
        "secondary_peak_exclusion_proved": False,
        "secondary_peak_exclusion_closed": False,
        "global_barrier_closed": False,
        "global_proof": False,
        "global_proof_closed": False,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "clay_promoted": False,
        "promotion_allowed": False,
        "artifact_complete": invariants_passed,
        "invariants_passed": invariants_passed,
        "invariant_failures": invariant_failures,
        "fail_closed": True,
        "exit_code": 0 if invariants_passed else 1,
        "control_card": {
            "O": (
                "Worker lane 2 owns only scripts/ns_sprint143_secondary_peak_exclusion_ledger.py "
                "and outputs/ns_sprint143_secondary_peak_exclusion_ledger/."
            ),
            "R": (
                "Normalize the theorem still needed: no secondary axial peak, "
                "shoulder, or off-route positive local maximum of v on the "
                "monitored interval."
            ),
            "C": (
                "Stdlib Python deterministic emitter with dataclass rows, "
                "stable SHA-256 hashes, validation, JSON, CSV, and Markdown."
            ),
            "S": (
                "Initial peak and symmetry support exist only locally; smoothing, "
                "nonlinear source terms, boundary/annular migration, missing "
                "zero-number theory, and missing constants keep the blocker open."
            ),
            "L": (
                "Sprint 138 secondary-peak blocker plus Sprint 140/142 ledgers "
                "imply a normalized theorem obligation, not a proof."
            ),
            "P": (
                "Use the artifact as a fail-closed ledger for future theorem work; "
                "do not use it as a global barrier certificate."
            ),
            "G": (
                "Validation passes only when secondary-peak exclusion, global "
                "barrier, global proof, Clay solution, and promotion flags are false."
            ),
            "F": (
                "Any missing required row, claimed theorem closure, hidden global "
                "barrier closure, missing constants closure, or promotion fails validation."
            ),
        },
    }


def validate_summary(summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    if summary["contract"] != CONTRACT:
        raise ValueError("wrong contract")
    if summary["sprint"] != SPRINT or summary["lane"] != LANE:
        raise ValueError("wrong sprint or lane metadata")
    if summary["normalized_theorem_needed"] != NORMALIZED_THEOREM_NEEDED:
        raise ValueError("wrong normalized theorem")
    for key in (
        "secondary_peak_exclusion_proved",
        "secondary_peak_exclusion_closed",
        "global_barrier_closed",
        "global_proof",
        "global_proof_closed",
        "full_clay_ns_solved",
        "clay_navier_stokes_promoted",
        "clay_promoted",
        "promotion_allowed",
    ):
        if summary[key]:
            raise ValueError("forbidden summary flag is true: " + key)
    if not summary["artifact_complete"] or not summary["invariants_passed"]:
        raise ValueError("artifact and invariants must pass")
    if summary["invariant_failures"]:
        raise ValueError("invariant failures: " + "; ".join(summary["invariant_failures"]))
    validate_rows(rows)


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = [
        "row_id",
        "ledger_role",
        "status",
        "normalized_claim_fragment",
        "support_available",
        "obstruction",
        "required_input",
        "barrier_consequence",
        "theorem_fragment_closed",
        "secondary_peak_exclusion_proved",
        "secondary_peak_exclusion_closed",
        "global_barrier_closed",
        "global_proof",
        "full_clay_ns_solved",
        "clay_navier_stokes_promoted",
        "promotion_allowed",
        "row_hash",
    ]
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            serialized = dict(row)
            for key in ("support_available", "obstruction", "required_input"):
                serialized[key] = " | ".join(serialized[key])
            writer.writerow({field: serialized[field] for field in fieldnames})


def render_markdown(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# Sprint 143 Secondary Peak Exclusion Ledger",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Program: `{summary['program']}`",
        f"- Parent gate: `{summary['parent_gate']}`",
        f"- Blocker: `{summary['blocker']}`",
        f"- Decision: `{summary['decision']}`",
        f"- Normalized theorem needed: `{summary['normalized_theorem_needed']}`",
        f"- Secondary peak exclusion proved: `{str(summary['secondary_peak_exclusion_proved']).lower()}`",
        f"- Secondary peak exclusion closed: `{str(summary['secondary_peak_exclusion_closed']).lower()}`",
        f"- Global barrier closed: `{str(summary['global_barrier_closed']).lower()}`",
        f"- Global proof: `{str(summary['global_proof']).lower()}`",
        f"- Full Clay NS solved: `{str(summary['full_clay_ns_solved']).lower()}`",
        f"- Clay Navier-Stokes promoted: `{str(summary['clay_navier_stokes_promoted']).lower()}`",
        f"- Artifact complete: `{str(summary['artifact_complete']).lower()}`",
        f"- Invariants passed: `{str(summary['invariants_passed']).lower()}`",
        f"- Rows hash: `{summary['rows_hash']}`",
        "",
        "## Rows",
        "",
        "| row_id | status | role | support | obstruction | required input |",
        "| --- | --- | --- | --- | --- | --- |",
    ]
    for row in rows:
        support = "; ".join(row["support_available"]).replace("|", "\\|")
        obstruction = "; ".join(row["obstruction"]).replace("|", "\\|")
        required = "; ".join(row["required_input"]).replace("|", "\\|")
        lines.append(
            "| {row_id} | {status} | {role} | {support} | {obstruction} | {required} |".format(
                row_id=row["row_id"],
                status=row["status"],
                role=row["ledger_role"],
                support=support,
                obstruction=obstruction,
                required=required,
            )
        )
    lines.extend(
        [
            "",
            "## Decision",
            "",
            (
                "The ledger does not prove SecondaryPeakExclusion. The normalized "
                "theorem remains a required input before the axial barrier can "
                "close, so no global proof or Clay promotion is emitted."
            ),
            "",
            "## Control Card",
            "",
        ]
    )
    for key, value in summary["control_card"].items():
        lines.append(f"- {key}: {value}")
    return "\n".join(lines) + "\n"


def emit(repo_root: Path, out_dir: Path) -> dict[str, Any]:
    if not out_dir.is_absolute():
        out_dir = repo_root / out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    rows = build_rows()
    summary = build_summary(repo_root, rows)
    validate_summary(summary, rows)

    summary_path = out_dir / SUMMARY_NAME
    rows_json_path = out_dir / ROWS_JSON_NAME
    rows_csv_path = out_dir / ROWS_CSV_NAME
    report_path = out_dir / REPORT_NAME

    write_json(rows_json_path, rows)
    write_csv(rows_csv_path, rows)
    report_path.write_text(render_markdown(summary, rows), encoding="utf-8")

    summary["artifacts"] = {
        "summary_json": display_path(summary_path, repo_root),
        "rows_json": display_path(rows_json_path, repo_root),
        "rows_csv": display_path(rows_csv_path, repo_root),
        "markdown": display_path(report_path, repo_root),
    }
    write_json(summary_path, summary)
    summary["artifact_hashes"] = {
        "summary_json": file_sha256(summary_path),
        "rows_json": file_sha256(rows_json_path),
        "rows_csv": file_sha256(rows_csv_path),
        "markdown": file_sha256(report_path),
    }
    write_json(summary_path, summary)
    return summary


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    summary = emit(repo_root=repo_root, out_dir=args.out_dir)
    print(
        json.dumps(
            {
                "artifact_complete": summary["artifact_complete"],
                "clay_navier_stokes_promoted": summary["clay_navier_stokes_promoted"],
                "contract": summary["contract"],
                "exit_code": summary["exit_code"],
                "full_clay_ns_solved": summary["full_clay_ns_solved"],
                "global_barrier_closed": summary["global_barrier_closed"],
                "global_proof": summary["global_proof"],
                "invariants_passed": summary["invariants_passed"],
                "secondary_peak_exclusion_closed": summary[
                    "secondary_peak_exclusion_closed"
                ],
                "secondary_peak_exclusion_proved": summary[
                    "secondary_peak_exclusion_proved"
                ],
            },
            sort_keys=True,
        )
    )
    return int(summary["exit_code"])


if __name__ == "__main__":
    sys.exit(main())
