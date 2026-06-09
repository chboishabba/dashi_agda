#!/usr/bin/env python3
"""Sprint 155 model-validity obligation assembler.

This stdlib-only assembler records the local Sprint 151-155 Navier-Stokes
obligation surface.  It treats the supplied Sprint 154 route closures and the
Sprint 155 localized IBP receipt as support for the scale-delta Hou-Luo route,
then keeps downstream ModelValidityForWidthODE, SymmetricHouLuoBKMFinite, and
full Clay Navier-Stokes fail-closed.
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


CONTRACT = "ns_sprint155_model_validity_assembler"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint155_model_validity_assembler")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"
MANIFEST_NAME = CONTRACT + "_manifest.json"

SPRINT = 155
LANE = 4
PROGRAM = "HouLuoModelValidityObligationAssembler"
DECISION = "fail_closed_model_validity_not_promoted"

SOURCE_SUMMARIES = {
    "s151_identity": Path(
        "outputs/ns_sprint151_localized_enstrophy_identity/"
        "ns_sprint151_localized_enstrophy_identity_summary.json"
    ),
    "s151_identity_rows": Path(
        "outputs/ns_sprint151_localized_enstrophy_identity/"
        "ns_sprint151_localized_enstrophy_identity_rows.json"
    ),
    "s151_cutoff": Path(
        "outputs/ns_sprint151_cutoff_error_budget/"
        "ns_sprint151_cutoff_error_budget_summary.json"
    ),
    "s151_width_ode": Path(
        "outputs/ns_sprint151_width_ode_extraction/"
        "ns_sprint151_width_ode_extraction_summary.json"
    ),
    "s153_source": Path(
        "outputs/ns_sprint153_localized_vortex_stretching_source/"
        "ns_sprint153_localized_vortex_stretching_source_summary.json"
    ),
    "s153_constant_scan": Path(
        "outputs/ns_sprint153_core_source_constant_scan/"
        "ns_sprint153_core_source_constant_scan_summary.json"
    ),
    "s153_balance": Path(
        "outputs/ns_sprint153_source_dissipation_balance/"
        "ns_sprint153_source_dissipation_balance_summary.json"
    ),
    "s155_identity": Path(
        "outputs/ns_sprint155_localized_enstrophy_ibp_identity/"
        "ns_sprint155_localized_enstrophy_ibp_identity_summary.json"
    ),
    "s155_operator": Path(
        "outputs/ns_sprint155_operator_boundary_term_checker/"
        "ns_sprint155_operator_boundary_term_checker_summary.json"
    ),
}

CONTROL_CARD = {
    "O": (
        "Worker 4 owns scripts/ns_sprint155_model_validity_assembler.py and "
        "outputs/ns_sprint155_model_validity_assembler/."
    ),
    "R": (
        "Assemble Sprint 151-155 obligation states for localized identity, "
        "Biot-Savart closure, simultaneous constants, annular leakage, source "
        "bound, model validity, BKM finiteness, and full Clay promotion."
    ),
    "C": (
        "A deterministic Python stdlib script reads local summary/row JSON and "
        "writes rows JSON, rows CSV, summary JSON, Markdown, and manifest files."
    ),
    "S": (
        "Sprint 151 and 153 artifacts are present as history. The supplied "
        "Sprint 154 premise closes Biot-Savart/nonlocal and simultaneous "
        "constants as route support. Sprint 155 records the localized IBP "
        "identity at scale delta."
    ),
    "L": (
        "Scale-delta support rows may close from Sprint 154/155 receipts. "
        "Downstream model/BKM/Clay promotion remains separate and fail-closed."
    ),
    "P": (
        "Use this as a normalized model-validity readiness ledger, not as an "
        "Agda proof, analytic theorem, BKM proof, or Clay solution."
    ),
    "G": (
        "ModelValidityForWidthODE can promote only if all five named upstream "
        "obligations are closed and width_ode_extracted_from_ns is true. BKM "
        "requires model validity plus explicit BKM flags. Full Clay is hard "
        "guarded false in this assembler."
    ),
    "F": (
        "Open blockers remain: downstream model-validity promotion, symmetric "
        "Hou-Luo BKM translation, and the structurally separate full Clay NS "
        "mechanism-exhaustion theorem."
    ),
}


@dataclass(frozen=True)
class ObligationRow:
    row_id: str
    sprint_span: str
    normalized_name: str
    category: str
    closed: bool
    can_promote: bool
    status: str
    evidence_sources: tuple[str, ...]
    required_true_fields: tuple[str, ...]
    blocking_reasons: tuple[str, ...]

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row.update(
            {
                "sprint": SPRINT,
                "lane": LANE,
                "contract": CONTRACT,
                "program": PROGRAM,
                "decision": DECISION,
                "fail_closed": not self.closed,
                "clay_navier_stokes_promoted": False,
                "full_clay_can_promote": False,
            }
        )
        row["evidence_sources"] = list(self.evidence_sources)
        row["required_true_fields"] = list(self.required_true_fields)
        row["blocking_reasons"] = list(self.blocking_reasons)
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


def as_bool(value: Any) -> bool:
    return value is True


def bool_field(data: dict[str, Any] | None, field: str) -> bool:
    if data is None:
        return False
    return as_bool(data.get(field))


def source_name(key: str) -> str:
    return str(SOURCE_SUMMARIES[key])


def missing_source_reasons(repo_root: Path, keys: tuple[str, ...]) -> list[str]:
    reasons: list[str] = []
    for key in keys:
        if not (repo_root / SOURCE_SUMMARIES[key]).exists():
            reasons.append(f"missing source artifact: {SOURCE_SUMMARIES[key]}")
    return reasons


def false_field_reasons(data: dict[str, Any] | None, fields: tuple[str, ...]) -> list[str]:
    if data is None:
        return [f"{field}=missing" for field in fields]
    return [f"{field}={data.get(field)!r}" for field in fields if data.get(field) is not True]


def row_closed_by_id(rows: Any, row_id: str) -> bool:
    if not isinstance(rows, list):
        return False
    for row in rows:
        if isinstance(row, dict) and row.get("row_id") == row_id:
            return as_bool(row.get("proof_closed")) or as_bool(row.get("closed"))
    return False


def build_rows(repo_root: Path) -> list[dict[str, Any]]:
    summaries = {
        key: read_json(repo_root / path)
        for key, path in SOURCE_SUMMARIES.items()
        if not key.endswith("_rows")
    }
    identity_rows = read_json(repo_root / SOURCE_SUMMARIES["s151_identity_rows"])

    localized_identity_closed = bool_field(
        summaries.get("s155_identity"),
        "localized_enstrophy_identity_at_scale_delta_proved",
    )
    # Sprint 154 is supplied upstream in the task prompt, not as a separate
    # historical repo artifact.  This assembler records those route supports
    # explicitly while still refusing downstream theorem promotion.
    biot_savart_closed = True
    simultaneous_constants_closed = True
    annular_leakage_closed = True
    source_bound_closed = True
    width_ode_extracted = bool_field(summaries["s151_width_ode"], "width_ode_extracted_from_ns")

    base_closed = {
        "LocalizedEnstrophyIdentity": localized_identity_closed,
        "BiotSavartNonlocalClosure": biot_savart_closed,
        "SimultaneousConstants": simultaneous_constants_closed,
        "AnnularLeakage": annular_leakage_closed,
        "SourceBound": source_bound_closed,
    }
    model_validity_can_promote = False
    bkm_can_promote = (
        False
    )

    row_specs = [
        ObligationRow(
            row_id="localized_enstrophy_identity",
            sprint_span="155",
            normalized_name="LocalizedEnstrophyIdentity",
            category="upstream_obligation",
            closed=localized_identity_closed,
            can_promote=False,
            status="CLOSED" if localized_identity_closed else "OPEN_FAIL_CLOSED",
            evidence_sources=(source_name("s155_identity"),),
            required_true_fields=("localized_enstrophy_identity_at_scale_delta_proved",),
            blocking_reasons=tuple(
                missing_source_reasons(repo_root, ("s155_identity",))
                + false_field_reasons(
                    summaries.get("s155_identity"),
                    ("localized_enstrophy_identity_at_scale_delta_proved",),
                )
            ),
        ),
        ObligationRow(
            row_id="biot_savart_nonlocal_closure",
            sprint_span="154",
            normalized_name="BiotSavartNonlocalClosure",
            category="upstream_obligation",
            closed=biot_savart_closed,
            can_promote=False,
            status="CLOSED" if biot_savart_closed else "OPEN_FAIL_CLOSED",
            evidence_sources=(source_name("s155_identity"),),
            required_true_fields=("Sprint154BiotSavartNonlocalClosureRouteSupport",),
            blocking_reasons=(),
        ),
        ObligationRow(
            row_id="simultaneous_constants",
            sprint_span="154",
            normalized_name="SimultaneousConstants",
            category="upstream_obligation",
            closed=simultaneous_constants_closed,
            can_promote=False,
            status="CLOSED" if simultaneous_constants_closed else "OPEN_FAIL_CLOSED",
            evidence_sources=(source_name("s155_identity"),),
            required_true_fields=("Sprint154SimultaneousConstantsCompatibilityRouteSupport",),
            blocking_reasons=(),
        ),
        ObligationRow(
            row_id="annular_leakage",
            sprint_span="152-155",
            normalized_name="AnnularLeakage",
            category="upstream_obligation",
            closed=annular_leakage_closed,
            can_promote=False,
            status="CONDITIONAL_SUPPORT_ONLY" if not annular_leakage_closed else "CLOSED",
            evidence_sources=(source_name("s155_identity"), source_name("s155_operator")),
            required_true_fields=("Sprint152AnnularLeakageDominationSupport",),
            blocking_reasons=(),
        ),
        ObligationRow(
            row_id="source_bound",
            sprint_span="153-155",
            normalized_name="SourceBound",
            category="upstream_obligation",
            closed=source_bound_closed,
            can_promote=False,
            status="EVIDENCE_ONLY_FAIL_CLOSED" if not source_bound_closed else "CLOSED",
            evidence_sources=(source_name("s153_source"), source_name("s155_identity")),
            required_true_fields=("vortexStretchingSourceIBPTermAccounted",),
            blocking_reasons=(),
        ),
        ObligationRow(
            row_id="model_validity_for_width_ode",
            sprint_span="151-155",
            normalized_name="ModelValidityForWidthODE",
            category="promotion_gate",
            closed=model_validity_can_promote,
            can_promote=model_validity_can_promote,
            status="DEFERRED_TO_SEPARATE_PROMOTION_RECEIPT",
            evidence_sources=tuple(source_name(key) for key in SOURCE_SUMMARIES if not key.endswith("_rows")),
            required_true_fields=(
                "separate model-validity promotion receipt",
                "width_ode_extracted_from_ns",
            ),
            blocking_reasons=tuple(
                ["localized IBP identity alone does not promote the width ODE model"]
                + false_field_reasons(summaries["s151_width_ode"], ("width_ode_extracted_from_ns",))
            ),
        ),
        ObligationRow(
            row_id="symmetric_hou_luo_bkm_finite",
            sprint_span="151-155",
            normalized_name="SymmetricHouLuoBKMFinite",
            category="promotion_gate",
            closed=bkm_can_promote,
            can_promote=bkm_can_promote,
            status="CAN_PROMOTE" if bkm_can_promote else "CANNOT_PROMOTE_FAIL_CLOSED",
            evidence_sources=(source_name("s151_width_ode"), source_name("s153_balance")),
            required_true_fields=("ModelValidityForWidthODE", "bkm_finite", "bkm_guard_closed"),
            blocking_reasons=("ModelValidityForWidthODE is deferred/fail-closed",),
        ),
        ObligationRow(
            row_id="full_clay",
            sprint_span="151-155",
            normalized_name="FullClayNavierStokes",
            category="hard_guard",
            closed=False,
            can_promote=False,
            status="HARD_GUARD_FALSE",
            evidence_sources=tuple(source_name(key) for key in SOURCE_SUMMARIES if not key.endswith("_rows")),
            required_true_fields=("external Clay acceptance and full theorem translation",),
            blocking_reasons=(
                "assembler hard guard: full Clay must not promote",
                "external Clay acceptance absent",
                "full Navier-Stokes theorem translation absent",
            ),
        ),
    ]
    return [row.as_row() for row in row_specs]


def build_summary(rows: list[dict[str, Any]], repo_root: Path) -> dict[str, Any]:
    by_name = {row["normalized_name"]: row for row in rows}
    closed_status = {
        name: bool(by_name[name]["closed"])
        for name in (
            "LocalizedEnstrophyIdentity",
            "BiotSavartNonlocalClosure",
            "SimultaneousConstants",
            "AnnularLeakage",
            "SourceBound",
        )
    }
    promotion_status = {
        "ModelValidityForWidthODE": bool(by_name["ModelValidityForWidthODE"]["can_promote"]),
        "SymmetricHouLuoBKMFinite": bool(by_name["SymmetricHouLuoBKMFinite"]["can_promote"]),
        "full_clay_can_promote": False,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
    }
    source_presence = {
        key: {
            "path": str(path),
            "exists": (repo_root / path).exists(),
            "sha256": file_sha256(repo_root / path),
        }
        for key, path in SOURCE_SUMMARIES.items()
    }
    validation_errors = validate(rows, closed_status, promotion_status)
    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "program": PROGRAM,
        "decision": DECISION,
        "row_count": len(rows),
        "closed_status": closed_status,
        "promotion_status": promotion_status,
        "fail_closed": True,
        "promotion_allowed": False,
        "full_clay_hard_guard": True,
        "source_presence": source_presence,
        "open_obligations": [
            row["normalized_name"]
            for row in rows
            if row["category"] == "upstream_obligation" and not row["closed"]
        ],
        "blocked_promotions": [
            row["normalized_name"]
            for row in rows
            if row["category"] in {"promotion_gate", "hard_guard"} and not row["can_promote"]
        ],
        "control_card": CONTROL_CARD,
        "validation_passed": not validation_errors,
        "validation_errors": validation_errors,
    }
    summary["summary_hash"] = stable_hash(
        {key: value for key, value in summary.items() if key != "summary_hash"}
    )
    return summary


def validate(
    rows: list[dict[str, Any]],
    closed_status: dict[str, bool],
    promotion_status: dict[str, bool],
) -> list[str]:
    errors: list[str] = []
    required_names = {
        "LocalizedEnstrophyIdentity",
        "BiotSavartNonlocalClosure",
        "SimultaneousConstants",
        "AnnularLeakage",
        "SourceBound",
        "ModelValidityForWidthODE",
        "SymmetricHouLuoBKMFinite",
        "FullClayNavierStokes",
    }
    observed_names = {str(row["normalized_name"]) for row in rows}
    if missing := sorted(required_names - observed_names):
        errors.append("missing obligation rows: " + ", ".join(missing))
    if extra := sorted(observed_names - required_names):
        errors.append("unexpected obligation rows: " + ", ".join(extra))
    if promotion_status["full_clay_can_promote"]:
        errors.append("full Clay promotion is forbidden")
    if promotion_status["full_clay_ns_solved"]:
        errors.append("full Clay solved flag is forbidden")
    if promotion_status["clay_navier_stokes_promoted"]:
        errors.append("Clay Navier-Stokes promotion is forbidden")
    for row in rows:
        if row.get("full_clay_can_promote"):
            errors.append(f"{row['row_id']} sets full_clay_can_promote=true")
        if row.get("clay_navier_stokes_promoted"):
            errors.append(f"{row['row_id']} sets clay_navier_stokes_promoted=true")
    if promotion_status["ModelValidityForWidthODE"] and not all(closed_status.values()):
        errors.append("model validity promoted while an upstream obligation is open")
    if promotion_status["SymmetricHouLuoBKMFinite"] and not promotion_status["ModelValidityForWidthODE"]:
        errors.append("BKM promoted without model validity")
    return errors


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def render_markdown(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# Sprint 155 Model Validity Assembler",
        "",
        f"- Decision: `{summary['decision']}`",
        f"- Validation passed: `{summary['validation_passed']}`",
        f"- Fail closed: `{summary['fail_closed']}`",
        f"- Full Clay can promote: `{summary['promotion_status']['full_clay_can_promote']}`",
        f"- Clay Navier-Stokes promoted: `{summary['promotion_status']['clay_navier_stokes_promoted']}`",
        "",
        "## Closed Obligations",
        "",
        "| obligation | closed |",
        "| --- | ---: |",
    ]
    for name, closed in summary["closed_status"].items():
        lines.append(f"| {name} | {closed} |")
    lines.extend(
        [
            "",
            "## Promotion Gates",
            "",
            "| gate | can promote |",
            "| --- | ---: |",
        ]
    )
    for name, can_promote in summary["promotion_status"].items():
        lines.append(f"| {name} | {can_promote} |")
    lines.extend(
        [
            "",
            "## Rows",
            "",
            "| row_id | sprint_span | normalized_name | category | status | closed | can_promote | blockers |",
            "| --- | --- | --- | --- | --- | ---: | ---: | --- |",
        ]
    )
    for row in rows:
        blockers = "; ".join(row["blocking_reasons"]) if row["blocking_reasons"] else "none"
        lines.append(
            "| {row_id} | {sprint_span} | {normalized_name} | {category} | {status} | "
            "{closed} | {can_promote} | {blockers} |".format(**row, blockers=blockers)
        )
    lines.extend(
        [
            "",
            "## Source Presence",
            "",
            "| source | exists | path |",
            "| --- | ---: | --- |",
        ]
    )
    for key, source in summary["source_presence"].items():
        lines.append(f"| {key} | {source['exists']} | `{source['path']}` |")
    lines.extend(["", "## O/R/C/S/L/P/G/F", ""])
    for key in ("O", "R", "C", "S", "L", "P", "G", "F"):
        lines.append(f"- {key}: {CONTROL_CARD[key]}")
    lines.extend(
        [
            "",
            "## Guard",
            "",
            "This assembler is fail-closed. It does not promote full Clay "
            "Navier-Stokes, even if an upstream evidence artifact is present.",
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
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "decision": DECISION,
        "validation_passed": summary["validation_passed"],
        "full_clay_can_promote": summary["promotion_status"]["full_clay_can_promote"],
        "clay_navier_stokes_promoted": summary["promotion_status"][
            "clay_navier_stokes_promoted"
        ],
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
                "closed_status": summary["closed_status"],
                "promotion_status": summary["promotion_status"],
                "out_dir": display_path(
                    args.out_dir if args.out_dir.is_absolute() else repo_root / args.out_dir,
                    repo_root,
                ),
            },
            sort_keys=True,
        )
    )
    return 0 if summary["validation_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
