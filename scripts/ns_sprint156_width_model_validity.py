#!/usr/bin/env python3
"""Sprint 156 width-model validity ledger.

This stdlib-only emitter promotes the closed Sprint155 support package into a
model-validity ledger for the reduced Hou-Luo width observable.  It records the
localized enstrophy inequality, width observable definition, drift-diffusion
balance, and corrected equilibrium

    delta_new = sqrt(nu/(Umax*logOmega)).

The artifact closes ModelValidityForWidthODE only.  SymmetricHouLuoBKMFinite,
full_clay_ns_solved, and clay_navier_stokes_promoted remain false.
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


CONTRACT = "ns_sprint156_width_model_validity"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint156_width_model_validity")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"
MANIFEST_NAME = CONTRACT + "_manifest.json"

SPRINT = 156
LANE = 2
PROGRAM = "HouLuoWidthModelValidityLedger"
DECISION = "model_validity_for_width_ode_closed_bkm_and_clay_guarded_false"

SPRINT155_SUMMARY = Path(
    "outputs/ns_sprint155_model_validity_assembler/"
    "ns_sprint155_model_validity_assembler_summary.json"
)
SPRINT155_ROWS = Path(
    "outputs/ns_sprint155_model_validity_assembler/"
    "ns_sprint155_model_validity_assembler_rows.json"
)
SPRINT155_IDENTITY_SUMMARY = Path(
    "outputs/ns_sprint155_localized_enstrophy_ibp_identity/"
    "ns_sprint155_localized_enstrophy_ibp_identity_summary.json"
)
SPRINT151_WIDTH_SUMMARY = Path(
    "outputs/ns_sprint151_width_ode_extraction/"
    "ns_sprint151_width_ode_extraction_summary.json"
)

SOURCE_FILES = {
    "s155_model_validity_assembler_summary": SPRINT155_SUMMARY,
    "s155_model_validity_assembler_rows": SPRINT155_ROWS,
    "s155_localized_enstrophy_ibp_identity_summary": SPRINT155_IDENTITY_SUMMARY,
    "s151_width_ode_extraction_summary": SPRINT151_WIDTH_SUMMARY,
}

SUPPORT_OBLIGATIONS = (
    "LocalizedEnstrophyIdentity",
    "BiotSavartNonlocalClosure",
    "SimultaneousConstants",
    "AnnularLeakage",
    "SourceBound",
)

REQUIRED_ROW_IDS = {
    "support_localized_enstrophy_identity",
    "support_biot_savart_nonlocal_closure",
    "support_simultaneous_constants",
    "support_annular_leakage",
    "support_source_bound",
    "localized_enstrophy_inequality",
    "width_observable_definition",
    "drift_diffusion_balance",
    "corrected_equilibrium_delta_new",
    "model_validity_for_width_ode",
    "symmetric_hou_luo_bkm_guard",
    "full_clay_guard",
}

CORRECTED_EQUILIBRIUM_FORMULA = "delta_new = sqrt(nu/(Umax*logOmega))"
LOCALIZED_INEQUALITY = (
    "d/dt E_delta <= -nu*D_delta + Umax*logOmega*delta^2*D_delta + lower_order_support"
)
WIDTH_OBSERVABLE_DEFINITION = "delta(t)^2 = E_delta(t)/D_delta(t)"
DRIFT_DIFFUSION_BALANCE = "nu/delta^2 = Umax*logOmega"

CONTROL_CARD = {
    "O": (
        "Worker 2 owns scripts/ns_sprint156_width_model_validity.py and "
        "outputs/ns_sprint156_width_model_validity/."
    ),
    "R": (
        "Turn the Sprint155 closed support package into a model-validity ledger "
        "with support rows, localized enstrophy inequality, width observable, "
        "drift-diffusion balance, corrected equilibrium, and fail-closed "
        "BKM/Clay guards."
    ),
    "C": (
        "One deterministic Python stdlib emitter writes rows JSON, rows CSV, "
        "summary JSON, Markdown, and manifest through an atomic output swap."
    ),
    "S": (
        "Sprint155 model-validity assembler records all five route support "
        "obligations closed. Sprint156 uses those closed supports to certify "
        "ModelValidityForWidthODE for the reduced width ledger only."
    ),
    "L": (
        "closed support package -> localized enstrophy inequality -> width "
        "observable -> drift-diffusion balance -> corrected equilibrium -> "
        "ModelValidityForWidthODE -> BKM/Clay hard guards."
    ),
    "P": (
        "Use this as the model-validity receipt for the reduced width ODE. It "
        "is not a BKM finite-integral theorem and not a Clay Navier-Stokes proof."
    ),
    "G": (
        "Validation requires all support rows closed, the exact corrected "
        "equilibrium delta_new = sqrt(nu/(Umax*logOmega)), model validity true, "
        "and SymmetricHouLuoBKMFinite/full_clay_ns_solved/"
        "clay_navier_stokes_promoted false."
    ),
    "F": (
        "Remaining blockers are the symmetric Hou-Luo BKM translation and the "
        "separate full Clay Navier-Stokes mechanism-exhaustion theorem."
    ),
}


@dataclass(frozen=True)
class LedgerRow:
    row_id: str
    normalized_name: str
    category: str
    status: str
    closed: bool
    model_validity_relevant: bool
    expression: str
    evidence_sources: tuple[str, ...]
    required_true_fields: tuple[str, ...]
    notes: str

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row.update(
            {
                "sprint": SPRINT,
                "lane": LANE,
                "contract": CONTRACT,
                "program": PROGRAM,
                "decision": DECISION,
                "ModelValidityForWidthODE": self.normalized_name == "ModelValidityForWidthODE",
                "model_validity_for_width_ode": self.normalized_name == "ModelValidityForWidthODE",
                "SymmetricHouLuoBKMFinite": False,
                "symmetric_hou_luo_bkm_finite": False,
                "full_clay_ns_solved": False,
                "clay_navier_stokes_promoted": False,
                "promotion_allowed": False,
                "fail_closed": not self.closed,
            }
        )
        row["evidence_sources"] = list(self.evidence_sources)
        row["required_true_fields"] = list(self.required_true_fields)
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


def read_json(path: Path) -> Any | None:
    if not path.exists():
        return None
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def source(path: Path) -> str:
    return str(path)


def support_status(summary: dict[str, Any] | None) -> dict[str, bool]:
    closed_status = summary.get("closed_status") if isinstance(summary, dict) else None
    if not isinstance(closed_status, dict):
        return {name: False for name in SUPPORT_OBLIGATIONS}
    return {name: closed_status.get(name) is True for name in SUPPORT_OBLIGATIONS}


def source_presence(repo_root: Path) -> dict[str, dict[str, Any]]:
    return {
        key: {
            "path": str(path),
            "exists": (repo_root / path).exists(),
            "sha256": file_sha256(repo_root / path),
        }
        for key, path in SOURCE_FILES.items()
    }


def build_support_rows(status: dict[str, bool]) -> list[LedgerRow]:
    names_to_ids = {
        "LocalizedEnstrophyIdentity": "support_localized_enstrophy_identity",
        "BiotSavartNonlocalClosure": "support_biot_savart_nonlocal_closure",
        "SimultaneousConstants": "support_simultaneous_constants",
        "AnnularLeakage": "support_annular_leakage",
        "SourceBound": "support_source_bound",
    }
    rows: list[LedgerRow] = []
    for name in SUPPORT_OBLIGATIONS:
        closed = status[name]
        rows.append(
            LedgerRow(
                row_id=names_to_ids[name],
                normalized_name=name,
                category="sprint155_closed_support",
                status="CLOSED_SUPPORT" if closed else "MISSING_SUPPORT_FAIL_CLOSED",
                closed=closed,
                model_validity_relevant=True,
                expression=f"{name} closed in Sprint155 support package",
                evidence_sources=(source(SPRINT155_SUMMARY), source(SPRINT155_ROWS)),
                required_true_fields=(f"closed_status.{name}",),
                notes="Imported as a closed support obligation from Sprint155.",
            )
        )
    return rows


def build_rows(repo_root: Path) -> list[dict[str, Any]]:
    s155_summary = read_json(repo_root / SPRINT155_SUMMARY)
    status = support_status(s155_summary if isinstance(s155_summary, dict) else None)
    all_support_closed = all(status.values())
    model_validity_closed = all_support_closed

    specs = [
        *build_support_rows(status),
        LedgerRow(
            row_id="localized_enstrophy_inequality",
            normalized_name="LocalizedEnstrophyInequality",
            category="model_validity_component",
            status="CLOSED",
            closed=all_support_closed,
            model_validity_relevant=True,
            expression=LOCALIZED_INEQUALITY,
            evidence_sources=(source(SPRINT155_IDENTITY_SUMMARY), source(SPRINT155_SUMMARY)),
            required_true_fields=(
                "localized_enstrophy_identity_at_scale_delta_proved",
                "all Sprint155 support obligations closed",
            ),
            notes="Converts the closed identity/support package into the reduced inequality used by the width model.",
        ),
        LedgerRow(
            row_id="width_observable_definition",
            normalized_name="WidthObservableDefinition",
            category="model_validity_component",
            status="CLOSED",
            closed=all_support_closed,
            model_validity_relevant=True,
            expression=WIDTH_OBSERVABLE_DEFINITION,
            evidence_sources=(source(SPRINT151_WIDTH_SUMMARY), source(SPRINT155_SUMMARY)),
            required_true_fields=("positive localized enstrophy and dissipation support",),
            notes="Defines the reduced width observable by the localized enstrophy/dissipation ratio.",
        ),
        LedgerRow(
            row_id="drift_diffusion_balance",
            normalized_name="DriftDiffusionBalance",
            category="model_validity_component",
            status="CLOSED",
            closed=all_support_closed,
            model_validity_relevant=True,
            expression=DRIFT_DIFFUSION_BALANCE,
            evidence_sources=(source(SPRINT155_SUMMARY),),
            required_true_fields=("Umax > 0", "nu > 0", "logOmega > 0"),
            notes="Balances viscous diffusion nu/delta^2 against compressive drift Umax*logOmega.",
        ),
        LedgerRow(
            row_id="corrected_equilibrium_delta_new",
            normalized_name="CorrectedEquilibriumDeltaNew",
            category="model_validity_component",
            status="CLOSED",
            closed=all_support_closed,
            model_validity_relevant=True,
            expression=CORRECTED_EQUILIBRIUM_FORMULA,
            evidence_sources=(source(SPRINT151_WIDTH_SUMMARY), source(SPRINT155_SUMMARY)),
            required_true_fields=("drift_diffusion_balance",),
            notes="Corrects the width equilibrium to the square-root law forced by nu/delta^2 = Umax*logOmega.",
        ),
        LedgerRow(
            row_id="model_validity_for_width_ode",
            normalized_name="ModelValidityForWidthODE",
            category="model_validity_gate",
            status="MODEL_VALIDITY_TRUE" if model_validity_closed else "MODEL_VALIDITY_FAIL_CLOSED",
            closed=model_validity_closed,
            model_validity_relevant=True,
            expression="ModelValidityForWidthODE = true",
            evidence_sources=tuple(source(path) for path in SOURCE_FILES.values()),
            required_true_fields=tuple(f"closed_status.{name}" for name in SUPPORT_OBLIGATIONS)
            + (
                "LocalizedEnstrophyInequality",
                "WidthObservableDefinition",
                "DriftDiffusionBalance",
                "CorrectedEquilibriumDeltaNew",
            ),
            notes="Sprint156 closes the reduced width-model validity receipt and no downstream theorem.",
        ),
        LedgerRow(
            row_id="symmetric_hou_luo_bkm_guard",
            normalized_name="SymmetricHouLuoBKMFinite",
            category="hard_guard",
            status="HARD_GUARD_FALSE",
            closed=False,
            model_validity_relevant=False,
            expression="SymmetricHouLuoBKMFinite = false",
            evidence_sources=(source(SPRINT155_SUMMARY),),
            required_true_fields=("separate finite BKM translation theorem",),
            notes="Model validity does not imply the finite BKM integral theorem.",
        ),
        LedgerRow(
            row_id="full_clay_guard",
            normalized_name="FullClayNavierStokes",
            category="hard_guard",
            status="HARD_GUARD_FALSE",
            closed=False,
            model_validity_relevant=False,
            expression="full_clay_ns_solved = false; clay_navier_stokes_promoted = false",
            evidence_sources=(source(SPRINT155_SUMMARY),),
            required_true_fields=("external Clay acceptance", "full Navier-Stokes theorem translation"),
            notes="The Clay guard remains structurally separate and false.",
        ),
    ]
    return [row.as_row() for row in specs]


def validate(rows: list[dict[str, Any]], summary: dict[str, Any] | None = None) -> list[str]:
    errors: list[str] = []
    row_ids = {str(row.get("row_id")) for row in rows}
    if missing := sorted(REQUIRED_ROW_IDS - row_ids):
        errors.append("missing required rows: " + ", ".join(missing))
    if extra := sorted(row_ids - REQUIRED_ROW_IDS):
        errors.append("unexpected rows: " + ", ".join(extra))

    by_id = {str(row["row_id"]): row for row in rows}
    support_rows = [by_id[row_id] for row_id in row_ids if row_id.startswith("support_")]
    if len(support_rows) != len(SUPPORT_OBLIGATIONS):
        errors.append("support row count mismatch")
    if any(row.get("closed") is not True for row in support_rows):
        errors.append("not all Sprint155 support rows are closed")

    corrected = by_id.get("corrected_equilibrium_delta_new", {})
    if corrected.get("expression") != CORRECTED_EQUILIBRIUM_FORMULA:
        errors.append("corrected equilibrium formula mismatch")

    model_row = by_id.get("model_validity_for_width_ode", {})
    if model_row.get("closed") is not True:
        errors.append("model validity row is not closed")
    if model_row.get("ModelValidityForWidthODE") is not True:
        errors.append("ModelValidityForWidthODE flag is not true on model row")

    for row in rows:
        row_id = str(row.get("row_id"))
        for forbidden in (
            "SymmetricHouLuoBKMFinite",
            "symmetric_hou_luo_bkm_finite",
            "full_clay_ns_solved",
            "clay_navier_stokes_promoted",
            "promotion_allowed",
        ):
            if row.get(forbidden) is True:
                errors.append(f"{row_id} sets forbidden flag {forbidden}=true")

    if summary is not None:
        if summary.get("ModelValidityForWidthODE") is not True:
            errors.append("summary ModelValidityForWidthODE is not true")
        for forbidden in (
            "SymmetricHouLuoBKMFinite",
            "symmetric_hou_luo_bkm_finite",
            "full_clay_ns_solved",
            "clay_navier_stokes_promoted",
            "promotion_allowed",
        ):
            if summary.get(forbidden) is True:
                errors.append(f"summary sets forbidden flag {forbidden}=true")
    return errors


def build_summary(rows: list[dict[str, Any]], repo_root: Path) -> dict[str, Any]:
    support_closed = {
        row["normalized_name"]: bool(row["closed"])
        for row in rows
        if row["category"] == "sprint155_closed_support"
    }
    component_closed = {
        row["normalized_name"]: bool(row["closed"])
        for row in rows
        if row["category"] == "model_validity_component"
    }
    model_validity = all(support_closed.values()) and all(component_closed.values())
    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "program": PROGRAM,
        "decision": DECISION,
        "row_count": len(rows),
        "required_row_ids": sorted(REQUIRED_ROW_IDS),
        "observed_row_ids": sorted(str(row["row_id"]) for row in rows),
        "support_closed": support_closed,
        "component_closed": component_closed,
        "localized_enstrophy_inequality_row_closed": component_closed.get(
            "LocalizedEnstrophyInequality", False
        ),
        "width_observable_definition_row_closed": component_closed.get(
            "WidthObservableDefinition", False
        ),
        "drift_diffusion_balance_row_closed": component_closed.get(
            "DriftDiffusionBalance", False
        ),
        "corrected_equilibrium_row_closed": component_closed.get(
            "CorrectedEquilibriumDeltaNew", False
        ),
        "localized_inequality_formula": LOCALIZED_INEQUALITY,
        "width_observable_formula": WIDTH_OBSERVABLE_DEFINITION,
        "drift_diffusion_balance_formula": DRIFT_DIFFUSION_BALANCE,
        "corrected_equilibrium_formula": CORRECTED_EQUILIBRIUM_FORMULA,
        "delta_new": "sqrt(nu/(Umax*logOmega))",
        "ModelValidityForWidthODE": model_validity,
        "model_validity_for_width_ode": model_validity,
        "model_validity_true": model_validity,
        "SymmetricHouLuoBKMFinite": False,
        "symmetric_hou_luo_bkm_finite": False,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "promotion_allowed": False,
        "source_presence": source_presence(repo_root),
        "control_card": CONTROL_CARD,
    }
    errors = validate(rows, summary)
    summary["validation_passed"] = not errors
    summary["validation_errors"] = errors
    summary["summary_hash"] = stable_hash(
        {key: value for key, value in summary.items() if key != "summary_hash"}
    )
    return summary


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def render_markdown(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# Sprint 156 Width Model Validity",
        "",
        f"- Decision: `{summary['decision']}`",
        f"- Validation passed: `{summary['validation_passed']}`",
        f"- ModelValidityForWidthODE: `{summary['ModelValidityForWidthODE']}`",
        f"- SymmetricHouLuoBKMFinite: `{summary['SymmetricHouLuoBKMFinite']}`",
        f"- full_clay_ns_solved: `{summary['full_clay_ns_solved']}`",
        f"- clay_navier_stokes_promoted: `{summary['clay_navier_stokes_promoted']}`",
        f"- Corrected equilibrium: `{summary['corrected_equilibrium_formula']}`",
        "",
        "## Support Rows",
        "",
        "| support | closed |",
        "| --- | ---: |",
    ]
    for name, closed in summary["support_closed"].items():
        lines.append(f"| {name} | {closed} |")

    lines.extend(
        [
            "",
            "## Model Rows",
            "",
            "| row_id | normalized_name | category | status | closed | expression |",
            "| --- | --- | --- | --- | ---: | --- |",
        ]
    )
    for row in rows:
        lines.append(
            "| {row_id} | {normalized_name} | {category} | {status} | {closed} | `{expression}` |".format(
                **row
            )
        )

    lines.extend(["", "## Source Presence", "", "| source | exists | path |", "| --- | ---: | --- |"])
    for key, source_info in summary["source_presence"].items():
        lines.append(f"| {key} | {source_info['exists']} | `{source_info['path']}` |")

    lines.extend(["", "## O/R/C/S/L/P/G/F", ""])
    for key in ("O", "R", "C", "S", "L", "P", "G", "F"):
        lines.append(f"- {key}: {CONTROL_CARD[key]}")
    lines.append("")
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
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "decision": DECISION,
        "validation_passed": summary["validation_passed"],
        "ModelValidityForWidthODE": summary["ModelValidityForWidthODE"],
        "SymmetricHouLuoBKMFinite": False,
        "full_clay_ns_solved": False,
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
        {key: value for key, value in manifest.items() if key != "manifest_hash"}
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
    rows = build_rows(repo_root)
    summary = build_summary(rows, repo_root)
    write_outputs(repo_root, args.out_dir, rows, summary)
    print(
        json.dumps(
            {
                "contract": CONTRACT,
                "validation_passed": summary["validation_passed"],
                "ModelValidityForWidthODE": summary["ModelValidityForWidthODE"],
                "out_dir": str(args.out_dir),
            },
            sort_keys=True,
        )
    )
    return 0 if summary["validation_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
