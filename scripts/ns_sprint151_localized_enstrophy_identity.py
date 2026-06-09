#!/usr/bin/env python3
"""Sprint 151 localized enstrophy identity ledger emitter.

This stdlib-only emitter records the localized enstrophy identity route state
for the Navier-Stokes/Hou-Luo width-ODE program.  It is a deterministic ledger,
not a proof artifact: it normalizes the identity terms, records the available
inputs and gaps, writes JSON/CSV outputs, and fails closed against any Clay or
finite-BKM promotion.
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


CONTRACT = "ns_sprint151_localized_enstrophy_identity"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint151_localized_enstrophy_identity")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"
MANIFEST_NAME = CONTRACT + "_manifest.json"

SPRINT = 151
LANE = 2
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
GATE = "LocalizedEnstrophyIdentityForModelWidthODE"
DECISION = "localized_enstrophy_identity_not_proved_fail_closed"

FAIL_CLOSED_FLAGS = {
    "localized_enstrophy_identity_proved": False,
    "model_validity_for_width_ode": False,
    "scaling_coupling_consistency": False,
    "symmetric_hou_luo_bkm_finite": False,
    "full_clay_ns_solved": False,
}

REQUIRED_ROW_IDS = {
    "localized_enstrophy_definition",
    "omega1_equation_input",
    "cutoff_derivative",
    "transport_flux",
    "diffusion_coercive_term",
    "boundary_annular_leakage",
    "vortex_stretching_source",
    "biot_savart_nonlocal_closure",
    "constants_compatibility",
    "model_width_ode_extraction",
    "clay_guard",
}

CONTROL_CARD = {
    "O": (
        "Lane 2 owns scripts/ns_sprint151_localized_enstrophy_identity.py and "
        "outputs/ns_sprint151_localized_enstrophy_identity/."
    ),
    "R": (
        "Emit a deterministic localized-enstrophy identity ledger with rows for "
        "definition, omega1 input, cutoff, flux, diffusion, leakage, stretching, "
        "Biot-Savart closure, constants, width-ODE extraction, and Clay guard."
    ),
    "C": (
        "The artifact is one stdlib Python emitter that writes rows JSON, rows "
        "CSV, summary JSON, Markdown, and a manifest through an atomic directory "
        "replacement."
    ),
    "S": (
        "The formal identity shape is ledgered, but cutoff leakage, nonlocal "
        "Biot-Savart control, simultaneous constants, and width-ODE validity "
        "remain open."
    ),
    "L": (
        "Rows are fixed by required IDs, hash-stamped with sorted JSON, and "
        "validated against exact fail-closed flags."
    ),
    "P": (
        "Use this as Sprint 151 accounting for missing localized enstrophy "
        "inputs; do not cite it as an Agda theorem, analytic closure, BKM "
        "finiteness proof, or Clay solution."
    ),
    "G": (
        "Validation passes only when all eleven rows exist, all requested proof "
        "and promotion flags are false, and the Clay guard blocks promotion."
    ),
    "F": (
        "Missing: rigorous localized identity closure with cutoff terms, "
        "compatible annular/boundary constants, nonlocal velocity closure, "
        "scaling-coupled width ODE, finite symmetric Hou-Luo BKM, and Clay NS."
    ),
}


@dataclass(frozen=True)
class LedgerRow:
    row_id: str
    normalized_name: str
    ledger_role: str
    identity_component: str
    formula_or_target: str
    sign_role: str
    available_input: tuple[str, ...]
    obstruction: tuple[str, ...]
    missing_input: tuple[str, ...]
    status: str
    supports_identity: bool
    adverse_or_unclosed: bool
    proof_closed: bool
    width_ode_ready: bool

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        for key in ("available_input", "obstruction", "missing_input"):
            row[key] = list(row[key])
        row["sprint"] = SPRINT
        row["lane"] = LANE
        row["contract"] = CONTRACT
        row["program"] = PROGRAM
        row["gate"] = GATE
        row["decision"] = DECISION
        row["fail_closed"] = True
        row["promotion_allowed"] = False
        row["clay_navier_stokes_promoted"] = False
        row.update(FAIL_CLOSED_FLAGS)
        row["claim_closed"] = False
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
        LedgerRow(
            row_id="localized_enstrophy_definition",
            normalized_name="LocalizedEnstrophyDefinition",
            ledger_role="definition",
            identity_component="E_phi(t) = 1/2 int phi_R(x,t) |omega(x,t)|^2 dx",
            formula_or_target=(
                "Differentiate E_phi with a smooth moving cutoff phi_R and "
                "account for transport, diffusion, stretching, and cutoff terms."
            ),
            sign_role="neutral_definition",
            available_input=("standard enstrophy density", "smooth compact cutoff template"),
            obstruction=("definition alone supplies no estimate",),
            missing_input=("closed localized identity theorem in the target geometry",),
            status="DEFINED_NOT_PROVED",
            supports_identity=True,
            adverse_or_unclosed=False,
            proof_closed=False,
            width_ode_ready=False,
        ),
        LedgerRow(
            row_id="omega1_equation_input",
            normalized_name="Omega1EquationInput",
            ledger_role="equation_input",
            identity_component="omega1 = omega^theta / r axisymmetric vorticity variable",
            formula_or_target="D_t omega1 = nu L_omega1 omega1 + 2 u1 partial_z u1",
            sign_role="source_equation_input",
            available_input=("axisymmetric omega1/u1 equation form",),
            obstruction=(
                "equation input is conditional on the axisymmetric-with-swirl reduction",
                "does not close the localized cutoff balance by itself",
            ),
            missing_input=("verified compatibility with every localized cutoff regime",),
            status="INPUT_RECORDED_CONDITIONAL",
            supports_identity=True,
            adverse_or_unclosed=False,
            proof_closed=False,
            width_ode_ready=False,
        ),
        LedgerRow(
            row_id="cutoff_derivative",
            normalized_name="CutoffDerivative",
            ledger_role="cutoff_commutator",
            identity_component="1/2 int (partial_t phi_R) |omega|^2 dx",
            formula_or_target=(
                "Control |partial_t phi_R|, |nabla phi_R|, and |Delta phi_R| "
                "by one active width and motion law."
            ),
            sign_role="adverse_unless_absorbed",
            available_input=("smooth radial/annular cutoff calculus",),
            obstruction=(
                "moving cutoff speed is not tied to a proved model width law",
                "cutoff derivative can leak enstrophy through the annulus",
            ),
            missing_input=("cutoff motion theorem compatible with width ODE extraction",),
            status="COMMUTATOR_OPEN",
            supports_identity=True,
            adverse_or_unclosed=True,
            proof_closed=False,
            width_ode_ready=False,
        ),
        LedgerRow(
            row_id="transport_flux",
            normalized_name="TransportFlux",
            ledger_role="transport_flux",
            identity_component="-1/2 int |omega|^2 u dot nabla phi_R dx",
            formula_or_target="Convert local transport into boundary/annular flux with controlled sign or size.",
            sign_role="adverse_boundary_flux",
            available_input=("divergence-free velocity transport form",),
            obstruction=(
                "flux sign is not fixed on moving annular boundaries",
                "velocity is nonlocal and can import exterior enstrophy into the active region",
            ),
            missing_input=("uniform inward/outward flux domination estimate",),
            status="FLUX_UNCLOSED",
            supports_identity=True,
            adverse_or_unclosed=True,
            proof_closed=False,
            width_ode_ready=False,
        ),
        LedgerRow(
            row_id="diffusion_coercive_term",
            normalized_name="DiffusionCoerciveTerm",
            ledger_role="diffusion",
            identity_component="-nu int phi_R |nabla omega|^2 dx plus cutoff diffusion errors",
            formula_or_target=(
                "Retain coercive dissipation after absorbing nabla phi_R and "
                "Delta phi_R localization errors."
            ),
            sign_role="favorable_with_cutoff_error",
            available_input=("viscous enstrophy integration by parts", "Young inequality"),
            obstruction=(
                "coercive term loses mass through cutoff-gradient errors",
                "axis/boundary integration terms need a compatible regularity ledger",
            ),
            missing_input=("single coercivity budget surviving cutoff and boundary errors",),
            status="COERCIVE_PARTIAL_NOT_CLOSED",
            supports_identity=True,
            adverse_or_unclosed=True,
            proof_closed=False,
            width_ode_ready=False,
        ),
        LedgerRow(
            row_id="boundary_annular_leakage",
            normalized_name="BoundaryAnnularLeakage",
            ledger_role="leakage",
            identity_component="annular shell terms from nabla phi_R, Delta phi_R, and moving support",
            formula_or_target=(
                "Bound all shell leakage by absorbable lower-order terms with "
                "constants shared by diffusion, flux, and stretching estimates."
            ),
            sign_role="adverse_leakage",
            available_input=("previous boundary/annular ledgers identify leakage channels",),
            obstruction=(
                "annular shell can contain source mass outside the local core",
                "boundary constants are not synchronized with nonlocal closure constants",
            ),
            missing_input=("boundary/annular leakage theorem with positive residual slack",),
            status="LEAKAGE_OPEN",
            supports_identity=False,
            adverse_or_unclosed=True,
            proof_closed=False,
            width_ode_ready=False,
        ),
        LedgerRow(
            row_id="vortex_stretching_source",
            normalized_name="VortexStretchingSource",
            ledger_role="stretching_source",
            identity_component="int phi_R omega dot (nabla u) omega dx",
            formula_or_target=(
                "Dominate localized vortex stretching by a signed source margin "
                "or an integrable width-dependent load."
            ),
            sign_role="main_adverse_source",
            available_input=("formal vorticity stretching term", "Hou-Luo source-route target"),
            obstruction=(
                "stretching term has no global sign",
                "source lower/upper balance is not coupled to the localized enstrophy width",
            ),
            missing_input=("rigorous localized stretching bound in the active Hou-Luo geometry",),
            status="SOURCE_UNCLOSED",
            supports_identity=True,
            adverse_or_unclosed=True,
            proof_closed=False,
            width_ode_ready=False,
        ),
        LedgerRow(
            row_id="biot_savart_nonlocal_closure",
            normalized_name="BiotSavartNonlocalClosure",
            ledger_role="nonlocal_velocity_closure",
            identity_component="u and nabla u reconstructed from omega through Biot-Savart",
            formula_or_target=(
                "Close velocity, strain, and cutoff-flux loads using a nonlocal "
                "kernel estimate on the same active scale."
            ),
            sign_role="nonlocal_adverse_or_margin_erasing",
            available_input=("axisymmetric Biot-Savart kernel route", "prior log-loss ledgers"),
            obstruction=(
                "near-coincident and off-axis kernel pieces can create log losses",
                "nonlocal exterior vorticity is not excluded by the localized identity",
            ),
            missing_input=("uniform Biot-Savart closure compatible with cutoff and constants",),
            status="NONLOCAL_CLOSURE_MISSING",
            supports_identity=False,
            adverse_or_unclosed=True,
            proof_closed=False,
            width_ode_ready=False,
        ),
        LedgerRow(
            row_id="constants_compatibility",
            normalized_name="ConstantsCompatibility",
            ledger_role="constant_budget",
            identity_component="one constant ledger for cutoff, flux, diffusion, leakage, source, and kernel terms",
            formula_or_target=(
                "Prove a positive residual after all adverse terms are charged "
                "against the same scale/time/boundary constants."
            ),
            sign_role="promotion_gate",
            available_input=("separate ledgers for several route hazards",),
            obstruction=(
                "separate estimates do not share a single residual inequality",
                "no proof that favorable diffusion/source margins dominate all leakage and nonlocal loads",
            ),
            missing_input=("simultaneous constants compatibility theorem",),
            status="CONSTANTS_INCOMPATIBLE_OR_UNPROVED",
            supports_identity=False,
            adverse_or_unclosed=True,
            proof_closed=False,
            width_ode_ready=False,
        ),
        LedgerRow(
            row_id="model_width_ode_extraction",
            normalized_name="ModelWidthODEExtraction",
            ledger_role="width_ode_extraction",
            identity_component="derive dW/dt or dE_phi/dt comparison model from the localized balance",
            formula_or_target=(
                "Extract a deterministic width ODE with validated scaling "
                "coupling from the localized enstrophy inequality."
            ),
            sign_role="model_validity_gate",
            available_input=("formal concentration-width route target",),
            obstruction=(
                "localized identity is not closed",
                "scaling coupling consistency is not proved",
                "nonlocal terms are not reduced to width-only coefficients",
            ),
            missing_input=("proved model-validity theorem for the width ODE",),
            status="WIDTH_ODE_NOT_VALIDATED",
            supports_identity=False,
            adverse_or_unclosed=True,
            proof_closed=False,
            width_ode_ready=False,
        ),
        LedgerRow(
            row_id="clay_guard",
            normalized_name="ClayGuard",
            ledger_role="promotion_guard",
            identity_component="fail-closed Navier-Stokes/Clay promotion guard",
            formula_or_target=(
                "Block promotion unless localized identity, width ODE validity, "
                "scaling consistency, finite BKM, and full Clay conditions are proved."
            ),
            sign_role="guard",
            available_input=("Sprint 151 requested fail-closed flags",),
            obstruction=("all requested promotion flags remain false",),
            missing_input=("full Clay Navier-Stokes solution",),
            status="FAIL_CLOSED_NOT_PROMOTED",
            supports_identity=False,
            adverse_or_unclosed=True,
            proof_closed=False,
            width_ode_ready=False,
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

    for key, expected in FAIL_CLOSED_FLAGS.items():
        if any(row.get(key) is not expected for row in rows):
            failures.append(f"row flag {key} does not match expected {expected!r}")
        if summary is not None and summary.get(key) is not expected:
            failures.append(f"summary flag {key} does not match expected {expected!r}")

    if any(row.get("promotion_allowed") is not False for row in rows):
        failures.append("row promotion_allowed must be false")
    if any(row.get("clay_navier_stokes_promoted") is not False for row in rows):
        failures.append("row clay_navier_stokes_promoted must be false")
    if any(row.get("claim_closed") is not False for row in rows):
        failures.append("row claim_closed must be false")
    if by_id.get("clay_guard", {}).get("status") != "FAIL_CLOSED_NOT_PROMOTED":
        failures.append("clay_guard status must be FAIL_CLOSED_NOT_PROMOTED")
    if summary is not None and summary.get("promotion_allowed") is not False:
        failures.append("summary promotion_allowed must be false")
    return failures


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    status_counts: dict[str, int] = {}
    role_counts: dict[str, int] = {}
    for row in rows:
        status = str(row["status"])
        role = str(row["ledger_role"])
        status_counts[status] = status_counts.get(status, 0) + 1
        role_counts[role] = role_counts.get(role, 0) + 1

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
        "role_counts": role_counts,
        "promotion_allowed": False,
        "clay_navier_stokes_promoted": False,
        "fail_closed": True,
        "artifact_complete": True,
        "control_card": CONTROL_CARD,
        "invariant_checked": False,
        "invariant_valid": False,
        "invariant_failures": [],
    }
    summary.update(FAIL_CLOSED_FLAGS)
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
        "# Sprint 151 Localized Enstrophy Identity",
        "",
        "## Decision",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Gate: `{summary['gate']}`",
        f"- Decision: `{summary['decision']}`",
        f"- Row count: `{summary['row_count']}`",
        f"- Localized enstrophy identity proved: `{summary['localized_enstrophy_identity_proved']}`",
        f"- Model validity for width ODE: `{summary['model_validity_for_width_ode']}`",
        f"- Scaling coupling consistency: `{summary['scaling_coupling_consistency']}`",
        f"- Symmetric Hou-Luo BKM finite: `{summary['symmetric_hou_luo_bkm_finite']}`",
        f"- Full Clay NS solved: `{summary['full_clay_ns_solved']}`",
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
            "| row_id | status | ledger_role | proof_closed | width_ode_ready |",
            "| --- | --- | --- | --- | --- |",
        ]
    )
    for row in rows:
        lines.append(
            "| {row_id} | {status} | {ledger_role} | {proof_closed} | {width_ode_ready} |".format(
                **row
            )
        )
    lines.extend(
        [
            "",
            "## Guard",
            "",
            (
                "This artifact records a fail-closed localized enstrophy ledger. "
                "It does not prove the localized identity, validate a model width "
                "ODE, prove scaling coupling consistency, prove finite symmetric "
                "Hou-Luo BKM, or solve the Clay Navier-Stokes problem."
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
    manifest.update(FAIL_CLOSED_FLAGS)
    manifest["promotion_allowed"] = False
    manifest["clay_navier_stokes_promoted"] = False
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
                "localized_enstrophy_identity_proved": summary[
                    "localized_enstrophy_identity_proved"
                ],
                "model_validity_for_width_ode": summary["model_validity_for_width_ode"],
                "scaling_coupling_consistency": summary["scaling_coupling_consistency"],
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
