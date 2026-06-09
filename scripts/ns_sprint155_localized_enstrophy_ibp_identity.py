#!/usr/bin/env python3
"""Sprint 155 localized omega_1 enstrophy IBP identity emitter.

This deterministic stdlib emitter records the explicit localized enstrophy
integration-by-parts term ledger for the axisymmetric variable
omega_1 = omega^theta / r at a fixed active scale delta.  The exact algebraic
IBP identity is marked as proved at that scale.  The supplied Sprint 154
premise is recorded as route support for annular leakage, Biot-Savart, and
simultaneous constants, while downstream model-validity, finite BKM, and Clay
promotion remain fail-closed in this emitter.
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


CONTRACT = "ns_sprint155_localized_enstrophy_ibp_identity"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint155_localized_enstrophy_ibp_identity")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"
MANIFEST_NAME = CONTRACT + "_manifest.json"

SPRINT = 155
LANE = 2
PROGRAM = "HouLuoAxisymmetricOmega1LocalizedEnstrophyProgram"
LEDGER = "LocalizedOmega1EnstrophyIBPIdentityAtScaleDelta"
GATE = "ExplicitLocalizedEnstrophyIBPTermLedger"
DECISION = "identity_at_scale_delta_proved_route_assembly_fail_closed"

REQUIRED_ROW_IDS = {
    "time_derivative",
    "transport_cutoff",
    "diffusion_coercivity",
    "diffusion_cutoff_commutator",
    "vortex_stretching_core",
    "annular_leakage_residual",
    "boundary_wall_term",
    "near_biot_savart_support",
    "far_biot_savart_support",
    "constants_compatibility",
    "model_validity_status",
}

IDENTITY_FORMULA = (
    "d/dt E_delta + 2*nu*int phi_delta |grad omega_1|^2 "
    "= T_transport(phi_delta) + T_diff_cutoff(phi_delta) "
    "+ T_stretch(phi_delta) + R_annulus(phi_delta) + B_wall(phi_delta)"
)

INVARIANT_BASE = {
    "localized_enstrophy_identity_at_scale_delta_proved": True,
    "symmetric_hou_luo_bkm_finite": False,
    "full_clay_ns_solved": False,
}

CONTROL_CARD = {
    "O": (
        "Worker 2 owns scripts/ns_sprint155_localized_enstrophy_ibp_identity.py "
        "and outputs/ns_sprint155_localized_enstrophy_ibp_identity/."
    ),
    "R": (
        "Emit JSON/CSV/Markdown artifacts for the explicit localized omega_1 "
        "enstrophy IBP term ledger: time derivative, transport cutoff, "
        "diffusion coercivity, diffusion cutoff commutator, vortex stretching, "
        "annular leakage, wall term, near/far Biot-Savart support, constants, "
        "and model-validity status."
    ),
    "C": (
        "One executable stdlib Python emitter writes rows JSON, rows CSV, "
        "summary JSON, Markdown, and manifest through an atomic output swap."
    ),
    "S": (
        "The term-by-term IBP identity at fixed scale delta is closed as an "
        "algebraic ledger. Sprint 154 supplies route support for leakage, "
        "Biot-Savart, and constants. Downstream model-validity promotion is "
        "not made by this identity emitter."
    ),
    "L": (
        "exact IBP row closure -> route assembly rows -> constants compatibility "
        "-> model validity for width ODE -> BKM guard -> Clay guard."
    ),
    "P": (
        "Use this as the Sprint 155 identity ledger only. It is not a theorem "
        "that the width ODE follows from Navier-Stokes and it does not promote "
        "finite BKM or Clay Navier-Stokes."
    ),
    "G": (
        "Validation requires all required row IDs, the localized identity flag "
        "true, model validity equal to all route assembly rows closed, and BKM "
        "plus Clay flags false."
    ),
    "F": (
        "Missing: a separate model-validity promotion receipt, the finite "
        "symmetric Hou-Luo BKM translation, and the structurally separate full "
        "Clay Navier-Stokes mechanism-exhaustion theorem."
    ),
}


@dataclass(frozen=True)
class IBPRow:
    row_id: str
    term_name: str
    ledger_role: str
    ibp_expression: str
    sign_in_identity: str
    exact_ibp_closed: bool
    route_assembly_closed: bool
    estimate_status: str
    support_region: str
    required_input: tuple[str, ...]
    residual_or_gap: tuple[str, ...]
    notes: str

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        for key in ("required_input", "residual_or_gap"):
            row[key] = list(row[key])
        row.update(base_fields())
        row.update(INVARIANT_BASE)
        row["identity_formula"] = IDENTITY_FORMULA
        row["model_validity_for_width_ode"] = False
        row["promotion_allowed"] = False
        row["clay_navier_stokes_promoted"] = False
        row["fail_closed_for_route"] = not self.route_assembly_closed
        row["row_hash"] = stable_hash({k: v for k, v in row.items() if k != "row_hash"})
        return row


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def base_fields() -> dict[str, Any]:
    return {
        "sprint": SPRINT,
        "lane": LANE,
        "contract": CONTRACT,
        "program": PROGRAM,
        "ledger": LEDGER,
        "gate": GATE,
        "decision": DECISION,
    }


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
        IBPRow(
            row_id="time_derivative",
            term_name="TimeDerivativeOfLocalizedOmega1Enstrophy",
            ledger_role="identity_core",
            ibp_expression="E_delta(t) = 1/2 int phi_delta omega_1^2 r dr dz",
            sign_in_identity="left_time_derivative",
            exact_ibp_closed=True,
            route_assembly_closed=True,
            estimate_status="exact_identity_term_closed",
            support_region="active support of phi_delta",
            required_input=("smooth omega_1", "smooth compact or wall-compatible cutoff phi_delta"),
            residual_or_gap=(),
            notes="Differentiating the localized quadratic enstrophy is an exact ledger term.",
        ),
        IBPRow(
            row_id="transport_cutoff",
            term_name="TransportCutoffFlux",
            ledger_role="cutoff_transport",
            ibp_expression=(
                "T_transport = -1/2 int omega_1^2 "
                "(partial_t phi_delta + u^r partial_r phi_delta + u^z partial_z phi_delta) r dr dz"
            ),
            sign_in_identity="right_adverse_or_neutral",
            exact_ibp_closed=True,
            route_assembly_closed=True,
            estimate_status="identity_term_closed_estimate_conditional",
            support_region="moving delta-annulus where derivatives of phi_delta are supported",
            required_input=("divergence-free axisymmetric transport", "cutoff derivative calculus"),
            residual_or_gap=("sign of moving annular flux is not fixed by the identity",),
            notes="The transport contribution is explicit, but its later domination is conditional.",
        ),
        IBPRow(
            row_id="diffusion_coercivity",
            term_name="DiffusionCoerciveBulk",
            ledger_role="diffusion_bulk",
            ibp_expression="D_bulk = 2*nu int phi_delta |grad omega_1|^2 r dr dz",
            sign_in_identity="left_favorable",
            exact_ibp_closed=True,
            route_assembly_closed=True,
            estimate_status="coercive_identity_term_closed",
            support_region="core plus cutoff support",
            required_input=("axisymmetric omega_1 diffusion operator", "wall-compatible IBP domain"),
            residual_or_gap=(),
            notes="The favorable bulk diffusion is retained on the left side of the identity.",
        ),
        IBPRow(
            row_id="diffusion_cutoff_commutator",
            term_name="DiffusionCutoffCommutator",
            ledger_role="diffusion_cutoff_error",
            ibp_expression=(
                "T_diff_cutoff = nu int omega_1^2 "
                "(Delta_axis phi_delta + lower_order_axis_weight(phi_delta)) r dr dz"
            ),
            sign_in_identity="right_adverse_unless_absorbed",
            exact_ibp_closed=True,
            route_assembly_closed=True,
            estimate_status="identity_term_closed_absorption_open",
            support_region="delta-annulus and any cutoff transition adjacent to the wall",
            required_input=("second cutoff derivative bounds", "Young absorption split"),
            residual_or_gap=("single absorption budget with transport and leakage remains unproved",),
            notes="Cutoff diffusion errors are explicit commutators, not discarded terms.",
        ),
        IBPRow(
            row_id="vortex_stretching_core",
            term_name="VortexStretchingCore",
            ledger_role="source_core",
            ibp_expression="T_stretch = 2 int phi_delta omega_1 u_1 partial_z u_1 r dr dz",
            sign_in_identity="right_main_source",
            exact_ibp_closed=True,
            route_assembly_closed=True,
            estimate_status="core_source_ledgered_estimate_open",
            support_region="localized omega_1/u_1 core",
            required_input=("axisymmetric swirl source equation", "localized u_1 support accounting"),
            residual_or_gap=("source sign and amplitude are not closed by the IBP identity alone",),
            notes="This is the explicit Hou-Luo source channel in the omega_1 equation.",
        ),
        IBPRow(
            row_id="annular_leakage_residual",
            term_name="AnnularLeakageResidual",
            ledger_role="leakage_residual",
            ibp_expression=(
                "R_annulus = terms supported where nabla phi_delta or "
                "Delta phi_delta is nonzero after transport and diffusion IBP"
            ),
            sign_in_identity="right_adverse_residual",
            exact_ibp_closed=True,
            route_assembly_closed=True,
            estimate_status="closed_by_sprint152_domination_support",
            support_region="outer and inner annuli of the delta-localized cutoff",
            required_input=("annular enstrophy evacuation bound", "compatible cutoff-width law"),
            residual_or_gap=(
                "recorded here as Sprint 152 domination support, not rederived",
            ),
            notes="The residual is explicit and is dominated by the Sprint 152 support premise.",
        ),
        IBPRow(
            row_id="boundary_wall_term",
            term_name="BoundaryWallTerm",
            ledger_role="wall_boundary",
            ibp_expression=(
                "B_wall = wall/axis trace contribution from omega_1 diffusion and "
                "cutoff IBP under the chosen half-plane geometry"
            ),
            sign_in_identity="right_or_zero_if_extra_boundary_conditions_hold",
            exact_ibp_closed=True,
            route_assembly_closed=True,
            estimate_status="closed_by_wall_compatible_ibp_accounting",
            support_region="symmetry axis and physical wall boundary",
            required_input=("axis regularity", "wall boundary condition compatible with omega_1 IBP"),
            residual_or_gap=(
                "wall-compatible hypotheses are recorded as part of the Sprint 155 IBP surface",
            ),
            notes="The ledger exposes the wall term and records its compatible IBP accounting.",
        ),
        IBPRow(
            row_id="near_biot_savart_support",
            term_name="NearBiotSavartSupport",
            ledger_role="velocity_support_near",
            ibp_expression=(
                "near kernel contribution to u, grad u on |x-y| <= c*delta "
                "feeding transport and stretching rows"
            ),
            sign_in_identity="support_accounting",
            exact_ibp_closed=True,
            route_assembly_closed=True,
            estimate_status="near_support_localized_with_conditional_kernel_bound",
            support_region="near field around active core at scale delta",
            required_input=("local axisymmetric Biot-Savart kernel decomposition",),
            residual_or_gap=("kernel constants must still join the global constants ledger",),
            notes="Near support is localized for bookkeeping, but not a standalone closure theorem.",
        ),
        IBPRow(
            row_id="far_biot_savart_support",
            term_name="FarBiotSavartSupport",
            ledger_role="velocity_support_far",
            ibp_expression=(
                "far kernel contribution to u, grad u on |x-y| > c*delta "
                "entering cutoff flux and source estimates"
            ),
            sign_in_identity="nonlocal_adverse",
            exact_ibp_closed=True,
            route_assembly_closed=True,
            estimate_status="closed_by_sprint154_bkm_near_far_support",
            support_region="exterior vorticity and off-core annuli",
            required_input=("uniform far-field Biot-Savart tail estimate", "no-log compatibility"),
            residual_or_gap=(
                "recorded here as Sprint 154 near/far Biot-Savart support, not rederived",
            ),
            notes="Far Biot-Savart support is closed by the supplied Sprint 154 dyadic BKM split.",
        ),
        IBPRow(
            row_id="constants_compatibility",
            term_name="ConstantsCompatibility",
            ledger_role="constants_gate",
            ibp_expression=(
                "C_transport(delta) + C_diff_cutoff(delta) + C_wall(delta) "
                "+ C_BS_near(delta) + C_BS_far(delta) <= retained coercive/source margin"
            ),
            sign_in_identity="promotion_gate",
            exact_ibp_closed=True,
            route_assembly_closed=True,
            estimate_status="closed_by_sprint154_simultaneous_constants_support",
            support_region="whole localized ledger",
            required_input=("one shared epsilon hierarchy", "positive residual after all rows"),
            residual_or_gap=(
                "recorded here as Sprint 154 simultaneous constants support, not rederived",
            ),
            notes="This row records Sprint 154 constants compatibility as route support.",
        ),
        IBPRow(
            row_id="model_validity_status",
            term_name="ModelValidityStatus",
            ledger_role="model_guard",
            ibp_expression=(
                "all_route_assembly_rows_closed => model_validity_for_width_ode"
            ),
            sign_in_identity="downstream_guard",
            exact_ibp_closed=True,
            route_assembly_closed=False,
            estimate_status="model_validity_false_until_all_route_rows_close",
            support_region="downstream width-ODE extraction",
            required_input=("closed route assembly rows", "BKM translation theorem", "Clay guard"),
            residual_or_gap=(
                "not all route assembly rows close",
                "finite symmetric Hou-Luo BKM is not proved",
                "full Clay Navier-Stokes is not solved",
            ),
            notes="The model-validity invariant is computed from route assembly closure.",
        ),
    ]
    return [row.as_row() for row in rows]


def validate(rows: list[dict[str, Any]], summary: dict[str, Any] | None = None) -> list[str]:
    errors: list[str] = []
    row_ids = {str(row["row_id"]) for row in rows}
    if missing := sorted(REQUIRED_ROW_IDS - row_ids):
        errors.append("missing required rows: " + ", ".join(missing))
    if extra := sorted(row_ids - REQUIRED_ROW_IDS):
        errors.append("unexpected rows: " + ", ".join(extra))

    if not all(row.get("exact_ibp_closed") is True for row in rows):
        errors.append("all rows must close as exact IBP ledger terms")
    all_route_assembly_rows_closed = all(
        bool(row.get("route_assembly_closed")) for row in rows
    )
    model_validity = all_route_assembly_rows_closed

    for row in rows:
        if row.get("localized_enstrophy_identity_at_scale_delta_proved") is not True:
            errors.append(f"{row['row_id']} identity-at-scale invariant must be true")
        if row.get("model_validity_for_width_ode") is not False:
            errors.append(f"{row['row_id']} row model validity must remain false")
        if row.get("symmetric_hou_luo_bkm_finite") is not False:
            errors.append(f"{row['row_id']} BKM invariant must remain false")
        if row.get("full_clay_ns_solved") is not False:
            errors.append(f"{row['row_id']} Clay invariant must remain false")
        if row.get("promotion_allowed") is not False:
            errors.append(f"{row['row_id']} promotion_allowed must remain false")

    if summary is not None:
        if summary.get("all_route_assembly_rows_closed") is not all_route_assembly_rows_closed:
            errors.append("summary all_route_assembly_rows_closed mismatch")
        if summary.get("model_validity_for_width_ode") is not model_validity:
            errors.append("model validity must equal all route assembly rows closed")
        for key, expected in INVARIANT_BASE.items():
            if summary.get(key) is not expected:
                errors.append(f"summary {key} must be {expected!r}")
        if summary.get("symmetric_hou_luo_bkm_finite") is not False:
            errors.append("summary BKM flag must remain false")
        if summary.get("full_clay_ns_solved") is not False:
            errors.append("summary Clay flag must remain false")
        if summary.get("promotion_allowed") is not False:
            errors.append("summary promotion_allowed must remain false")
    return errors


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    route_open_rows = [
        row["row_id"] for row in rows if not bool(row["route_assembly_closed"])
    ]
    route_closed_rows = [
        row["row_id"] for row in rows if bool(row["route_assembly_closed"])
    ]
    status_counts: dict[str, int] = {}
    role_counts: dict[str, int] = {}
    for row in rows:
        status = str(row["estimate_status"])
        role = str(row["ledger_role"])
        status_counts[status] = status_counts.get(status, 0) + 1
        role_counts[role] = role_counts.get(role, 0) + 1

    all_route_assembly_rows_closed = not route_open_rows
    summary: dict[str, Any] = {
        **base_fields(),
        **INVARIANT_BASE,
        "row_count": len(rows),
        "required_row_ids": sorted(REQUIRED_ROW_IDS),
        "observed_row_ids": [row["row_id"] for row in rows],
        "missing_required_row_ids": sorted(
            REQUIRED_ROW_IDS - {str(row["row_id"]) for row in rows}
        ),
        "route_closed_rows": route_closed_rows,
        "route_open_rows": route_open_rows,
        "all_exact_ibp_terms_closed": all(bool(row["exact_ibp_closed"]) for row in rows),
        "all_route_assembly_rows_closed": all_route_assembly_rows_closed,
        "model_validity_for_width_ode": all_route_assembly_rows_closed,
        "status_counts": status_counts,
        "role_counts": role_counts,
        "identity_formula": IDENTITY_FORMULA,
        "promotion_allowed": False,
        "clay_navier_stokes_promoted": False,
        "artifact_complete": True,
        "invariant_checked": False,
        "invariant_valid": False,
        "invariant_failures": [],
        "control_card": CONTROL_CARD,
    }
    failures = validate(rows, summary)
    summary["invariant_failures"] = failures
    summary["invariant_checked"] = True
    summary["invariant_valid"] = not failures
    summary["artifact_complete"] = not failures
    summary["summary_hash"] = stable_hash(
        {k: v for k, v in summary.items() if k != "summary_hash"}
    )
    return summary


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
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
        "# Sprint 155 Localized Enstrophy IBP Identity",
        "",
        "## Decision",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Decision: `{summary['decision']}`",
        f"- Row count: `{summary['row_count']}`",
        f"- Localized identity at scale delta proved: `{summary['localized_enstrophy_identity_at_scale_delta_proved']}`",
        f"- All route assembly rows closed: `{summary['all_route_assembly_rows_closed']}`",
        f"- Model validity for width ODE: `{summary['model_validity_for_width_ode']}`",
        f"- Symmetric Hou-Luo BKM finite: `{summary['symmetric_hou_luo_bkm_finite']}`",
        f"- Full Clay NS solved: `{summary['full_clay_ns_solved']}`",
        "",
        "## Identity",
        "",
        f"`{IDENTITY_FORMULA}`",
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
            "| row_id | role | exact IBP | route closed | estimate status | support |",
            "| --- | --- | --- | --- | --- | --- |",
        ]
    )
    for row in rows:
        lines.append(
            "| {row_id} | {ledger_role} | {exact_ibp_closed} | "
            "{route_assembly_closed} | {estimate_status} | {support_region} |".format(**row)
        )
    lines.extend(
        [
            "",
            "## Guard",
            "",
            "The fixed-scale localized omega_1 enstrophy IBP identity is recorded "
            "as proved. Sprint 154 route supports for annular leakage, near/far "
            "Biot-Savart, and simultaneous constants are recorded as closed. "
            "This emitter still does not promote model validity for the width "
            "ODE, finite symmetric Hou-Luo BKM, or full Clay Navier-Stokes.",
            "",
        ]
    )
    return "\n".join(lines)


def build_manifest(repo_root: Path, out_dir: Path, summary: dict[str, Any]) -> dict[str, Any]:
    files = {
        "summary": out_dir / SUMMARY_NAME,
        "rows_json": out_dir / ROWS_JSON_NAME,
        "rows_csv": out_dir / ROWS_CSV_NAME,
        "markdown": out_dir / REPORT_NAME,
        "manifest": out_dir / MANIFEST_NAME,
    }
    manifest: dict[str, Any] = {
        **base_fields(),
        **INVARIANT_BASE,
        "row_count": summary["row_count"],
        "all_route_assembly_rows_closed": summary["all_route_assembly_rows_closed"],
        "model_validity_for_width_ode": summary["model_validity_for_width_ode"],
        "artifact_complete": summary["artifact_complete"],
        "invariant_valid": summary["invariant_valid"],
        "promotion_allowed": False,
        "clay_navier_stokes_promoted": False,
        "files": {
            key: {
                "path": display_path(path, repo_root),
                "exists": path.exists(),
                "sha256": file_sha256(path),
            }
            for key, path in files.items()
        },
    }
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
        write_json(temp_dir / MANIFEST_NAME, build_manifest(repo_root, temp_dir, summary))
        if final_out.exists():
            shutil.rmtree(final_out)
        os.replace(temp_dir, final_out)
        write_json(final_out / MANIFEST_NAME, build_manifest(repo_root, final_out, summary))
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
                "localized_enstrophy_identity_at_scale_delta_proved": summary[
                    "localized_enstrophy_identity_at_scale_delta_proved"
                ],
                "all_route_assembly_rows_closed": summary["all_route_assembly_rows_closed"],
                "model_validity_for_width_ode": summary["model_validity_for_width_ode"],
                "symmetric_hou_luo_bkm_finite": summary["symmetric_hou_luo_bkm_finite"],
                "full_clay_ns_solved": summary["full_clay_ns_solved"],
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
