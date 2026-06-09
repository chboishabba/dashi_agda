#!/usr/bin/env python3
"""Sprint 162 critical residual boundary summary emitter."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import shutil
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint162_critical_residual_boundary"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SUMMARY_NAME = f"{CONTRACT}_summary.json"
ROWS_JSON_NAME = f"{CONTRACT}_rows.json"
ROWS_CSV_NAME = f"{CONTRACT}_rows.csv"
MARKDOWN_NAME = f"{CONTRACT}.md"
MANIFEST_NAME = f"{CONTRACT}_manifest.json"
SPRINT = 162
LANE = 1

RESIDUAL_COMPONENTS = (
    "LocalDefect",
    "PressureFlux",
    "StretchingAlignment",
    "Dissipation",
    "NSCriticalResidual",
)

CLAY_AND_PROMOTION_FLAGS = (
    "MechanismExhaustionForFullClayNS",
    "NoPersistentPositiveNSCriticalResidual",
    "PressureStretchingDepletionLemma",
    "full_clay_ns_solved",
    "fullClayNSSolved",
    "clay_navier_stokes_promoted",
    "ClayNavierStokesPromoted",
    "ClaySubmissionReady",
    "ClaySubmissionPromotionPacket",
    "promotion_allowed",
    "residual_depletion_theorem_promoted",
)

REQUIRED_OPEN_LEMMAS = (
    "LocalDefectAbsorptionLemmaOpen",
    "PressureFluxSignClosureLemmaOpen",
    "StretchingAlignmentDepletionLemmaOpen",
    "DissipationDominanceLemmaOpen",
    "NSCriticalResidualDepletionTheoremOpen",
)

CONTROL_CARD = {
    "O": "Sprint162 lane 1 owns the critical residual boundary summary.",
    "R": "Record the residual-positive critical profile without promoting Clay Navier-Stokes or a residual depletion theorem.",
    "C": "Single stdlib Python emitter writes outputs/ns_sprint162_critical_residual_boundary/summary.json.",
    "S": "Residual terms are classified as boundary evidence only: LocalDefect, PressureFlux, StretchingAlignment, Dissipation, and NSCriticalResidual.",
    "L": "local defect + pressure flux + stretching alignment - dissipation -> positive critical residual profile -> fail-closed theorem boundary.",
    "P": "Use the artifact to block promotion until each residual-depletion lemma is supplied by a separate proof lane.",
    "G": "Validation passes only when Clay/promotion flags are false and no required open lemma is asserted as closed.",
    "F": "The residual depletion theorem remains false for Sprint162.",
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", "--output-dir", dest="out_dir", type=Path, default=OUT_DIR_DEFAULT)
    parser.add_argument(
        "--generated-at",
        default=None,
        help="ISO-8601 timestamp to place in generated_at_utc; defaults to current UTC time.",
    )
    return parser.parse_args()


def stable_hash(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def fail_closed_flags(names: tuple[str, ...]) -> dict[str, bool]:
    return {name: False for name in names}


def build_component_rows() -> list[dict[str, Any]]:
    specs = [
        {
            "component": "LocalDefect",
            "role": "localized cutoff and commutator defect",
            "signed_contribution": "+",
            "boundary_status": "UNABSORBED_RESIDUAL_SOURCE",
            "required_open_lemma": "LocalDefectAbsorptionLemmaOpen",
            "residual_positive_weight": 2,
        },
        {
            "component": "PressureFlux",
            "role": "nonlocal pressure flux through the localized boundary",
            "signed_contribution": "+",
            "boundary_status": "SIGN_INDEFINITE_PRESSURE_SOURCE",
            "required_open_lemma": "PressureFluxSignClosureLemmaOpen",
            "residual_positive_weight": 3,
        },
        {
            "component": "StretchingAlignment",
            "role": "alignment-sensitive vortex stretching source",
            "signed_contribution": "+",
            "boundary_status": "ALIGNMENT_DEPLETION_NOT_ESTABLISHED",
            "required_open_lemma": "StretchingAlignmentDepletionLemmaOpen",
            "residual_positive_weight": 4,
        },
        {
            "component": "Dissipation",
            "role": "viscous dissipation available inside the localized budget",
            "signed_contribution": "-",
            "boundary_status": "INSUFFICIENT_TO_DOMINATE_SOURCES",
            "required_open_lemma": "DissipationDominanceLemmaOpen",
            "residual_positive_weight": -3,
        },
        {
            "component": "NSCriticalResidual",
            "role": "net residual left after source and dissipation accounting",
            "signed_contribution": "+",
            "boundary_status": "POSITIVE_PROFILE_REMAINS",
            "required_open_lemma": "NSCriticalResidualDepletionTheoremOpen",
            "residual_positive_weight": 6,
        },
    ]
    rows: list[dict[str, Any]] = []
    for index, spec in enumerate(specs, start=1):
        row: dict[str, Any] = {
            "row_id": f"R{index:02d}",
            "sprint": SPRINT,
            "lane": LANE,
            "contract": CONTRACT,
            **spec,
            "component_required": spec["component"] in RESIDUAL_COMPONENTS,
            "clay_boundary_only": True,
            "residual_depletion_supplied": False,
        }
        row.update(fail_closed_flags(CLAY_AND_PROMOTION_FLAGS))
        row.update(fail_closed_flags(REQUIRED_OPEN_LEMMAS))
        row["row_hash"] = stable_hash({key: value for key, value in row.items() if key != "row_hash"})
        rows.append(row)
    return rows


def all_named_flags_false(record: dict[str, Any], names: tuple[str, ...]) -> bool:
    return all(record.get(name) is False for name in names)


def rows_named_flags_false(rows: list[dict[str, Any]], names: tuple[str, ...]) -> bool:
    return all(all_named_flags_false(row, names) for row in rows)


def build_summary(repo_root: Path, out_dir: Path, generated_at: str) -> dict[str, Any]:
    rows = build_component_rows()
    components_present = tuple(row["component"] for row in rows)
    residual_positive_score = sum(row["residual_positive_weight"] for row in rows)
    source_score = sum(row["residual_positive_weight"] for row in rows if row["signed_contribution"] == "+")
    dissipation_score = -sum(row["residual_positive_weight"] for row in rows if row["signed_contribution"] == "-")
    residual_positive_profile = residual_positive_score > 0 and source_score > dissipation_score

    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "generated_at": generated_at,
        "repo_root": str(repo_root),
        "out_dir": str(out_dir),
        "summary_path": str(out_dir / SUMMARY_NAME),
        "surface_name": "CriticalResidualBoundary",
        "decision": "critical_residual_boundary_fail_closed",
        "residual_boundary_components": list(RESIDUAL_COMPONENTS),
        "component_rows": rows,
        "component_count": len(rows),
        "components_present": list(components_present),
        "components_complete": components_present == RESIDUAL_COMPONENTS,
        "source_positive_score": source_score,
        "dissipation_score": dissipation_score,
        "residual_positive_score": residual_positive_score,
        "residual_positive_profile": residual_positive_profile,
        "residual_positive_profile_name": "LocalDefect+PressureFlux+StretchingAlignment+Dissipation=>NSCriticalResidual",
        "residual_depletion_theorem": False,
        "residual_depletion_theorem_false": True,
        "required_open_lemmas": list(REQUIRED_OPEN_LEMMAS),
        "required_open_lemmas_false": rows_named_flags_false(rows, REQUIRED_OPEN_LEMMAS),
        "row_clay_and_promotion_flags_false": rows_named_flags_false(rows, CLAY_AND_PROMOTION_FLAGS),
        "control_card": CONTROL_CARD,
    }
    summary.update(fail_closed_flags(CLAY_AND_PROMOTION_FLAGS))
    summary.update(fail_closed_flags(REQUIRED_OPEN_LEMMAS))
    summary["summary_clay_and_promotion_flags_false"] = all_named_flags_false(summary, CLAY_AND_PROMOTION_FLAGS)
    summary["summary_required_open_lemmas_false"] = all_named_flags_false(summary, REQUIRED_OPEN_LEMMAS)
    summary["validation_passed"] = (
        summary["components_complete"]
        and summary["residual_positive_profile"]
        and summary["residual_depletion_theorem_false"]
        and summary["row_clay_and_promotion_flags_false"]
        and summary["summary_clay_and_promotion_flags_false"]
        and summary["required_open_lemmas_false"]
        and summary["summary_required_open_lemmas_false"]
    )
    summary["summary_hash"] = stable_hash({key: value for key, value in summary.items() if key != "summary_hash"})
    return summary


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# Sprint 162 Critical Residual Boundary",
        "",
        f"- Surface: `{summary['surface_name']}`",
        f"- Decision: `{summary['decision']}`",
        f"- Residual-positive profile: `{summary['residual_positive_profile']}`",
        f"- Residual depletion theorem: `{summary['residual_depletion_theorem']}`",
        f"- Validation passed: `{summary['validation_passed']}`",
        "",
        "| component | sign | boundary_status | open_lemma |",
        "| --- | --- | --- | --- |",
    ]
    for row in summary["component_rows"]:
        lines.append(
            f"| {row['component']} | {row['signed_contribution']} | "
            f"{row['boundary_status']} | {row['required_open_lemma']} |"
        )
    lines.extend(["", "## O/R/C/S/L/P/G/F", ""])
    for key in ("O", "R", "C", "S", "L", "P", "G", "F"):
        lines.append(f"- {key}: {CONTROL_CARD[key]}")
    lines.append("")
    return "\n".join(lines)


def file_sha256(path: Path) -> str | None:
    if not path.exists():
        return None
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def build_manifest(out_dir: Path, summary: dict[str, Any]) -> dict[str, Any]:
    files = {
        "summary": out_dir / SUMMARY_NAME,
        "rows_json": out_dir / ROWS_JSON_NAME,
        "rows_csv": out_dir / ROWS_CSV_NAME,
        "markdown": out_dir / MARKDOWN_NAME,
        "manifest": out_dir / MANIFEST_NAME,
    }
    manifest = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "generated_at": summary["generated_at"],
        "validation_passed": summary["validation_passed"],
        "files": {
            key: {"path": str(path), "exists": path.exists(), "sha256": file_sha256(path)}
            for key, path in files.items()
        },
    }
    manifest["manifest_hash"] = stable_hash({key: value for key, value in manifest.items() if key != "manifest_hash"})
    return manifest


def resolve_path(path: Path, repo_root: Path) -> Path:
    return path if path.is_absolute() else repo_root / path


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = resolve_path(args.out_dir, repo_root)
    generated_at = args.generated_at or datetime.now(timezone.utc).isoformat()

    summary = build_summary(repo_root=repo_root, out_dir=out_dir, generated_at=generated_at)

    out_dir.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=f".{CONTRACT}.", dir=out_dir.parent) as temp_name:
        temp_dir = Path(temp_name)
        write_json(temp_dir / ROWS_JSON_NAME, summary["component_rows"])
        write_csv(temp_dir / ROWS_CSV_NAME, summary["component_rows"])
        write_json(temp_dir / SUMMARY_NAME, summary)
        (temp_dir / MARKDOWN_NAME).write_text(render_markdown(summary), encoding="utf-8")
        write_json(temp_dir / MANIFEST_NAME, build_manifest(temp_dir, summary))
        if out_dir.exists():
            shutil.rmtree(out_dir)
        os.replace(temp_dir, out_dir)
        write_json(out_dir / MANIFEST_NAME, build_manifest(out_dir, summary))

    print(
        json.dumps(
            {
                "contract": CONTRACT,
                "summary": str(out_dir / SUMMARY_NAME),
                "validation_passed": summary["validation_passed"],
            },
            sort_keys=True,
        )
    )
    return 0 if summary["validation_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
