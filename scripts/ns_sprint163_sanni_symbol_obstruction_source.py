#!/usr/bin/env python3
"""Sprint 163 lane 2 Sanni symbol obstruction source emitter."""

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


CONTRACT = "ns_sprint163_sanni_symbol_obstruction_source"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SUMMARY_NAME = f"{CONTRACT}_summary.json"
ROWS_JSON_NAME = f"{CONTRACT}_rows.json"
ROWS_CSV_NAME = f"{CONTRACT}_rows.csv"
MARKDOWN_NAME = f"{CONTRACT}.md"
MANIFEST_NAME = f"{CONTRACT}_manifest.json"
SPRINT = 163
LANE = 2

PROTOCOL_TITLE = (
    "A Topological Obstruction to Persistent Vorticity Alignment via the "
    "Angular Strain Symbol"
)
PROTOCOL_AUTHOR = "Torah Sanni"
PROTOCOL_DOI_URL = "https://dx.doi.org/10.17504/protocols.io.j8nlk15m5g5r/v1"
PROTOCOL_CREATED = "2025-12-26"
PROTOCOL_MODIFIED = "2026-05-18"
PROTOCOL_CREATED_LABEL = "Dec 26 2025"
PROTOCOL_MODIFIED_LABEL = "May 18 2026"

CLAY_PDE_PROMOTION_FLAGS = (
    "MechanismExhaustionForFullClayNS",
    "ClayNavierStokesSolved",
    "ClayNavierStokesPromoted",
    "clay_navier_stokes_promoted",
    "full_clay_ns_solved",
    "fullClayNSSolved",
    "fullNavierStokesRegularityProved",
    "fullNavierStokesSolutionConstructed",
    "pde_regular_class_promoted",
    "PDERegularityClaim",
    "PDEBlowupClaim",
    "pde_blowup_claim",
    "blowup_claim_promoted",
    "regularity_claim_promoted",
    "promotion_allowed",
    "ClaySubmissionReady",
)

SOURCE_ROWS = (
    {
        "row_id": "S01",
        "source_field": "title",
        "source_value": PROTOCOL_TITLE,
        "source_status": "SOURCE_BOUND_METADATA",
        "symbol_level_role": "names the finite-dimensional obstruction protocol surface",
    },
    {
        "row_id": "S02",
        "source_field": "doi_url",
        "source_value": PROTOCOL_DOI_URL,
        "source_status": "SOURCE_BOUND_METADATA",
        "symbol_level_role": "canonical protocols.io DOI URL for the source packet",
    },
    {
        "row_id": "S03",
        "source_field": "created",
        "source_value": PROTOCOL_CREATED_LABEL,
        "source_status": "SOURCE_BOUND_METADATA",
        "symbol_level_role": "source creation date recorded without mathematical promotion",
    },
    {
        "row_id": "S04",
        "source_field": "modified",
        "source_value": PROTOCOL_MODIFIED_LABEL,
        "source_status": "SOURCE_BOUND_METADATA",
        "symbol_level_role": "source modification date recorded without mathematical promotion",
    },
    {
        "row_id": "S05",
        "source_field": "scope",
        "source_value": "finite-dimensional symbol-level only",
        "source_status": "SCOPE_BOUNDARY",
        "symbol_level_role": "blocks transfer from symbolic obstruction metadata to PDE regularity",
    },
    {
        "row_id": "S06",
        "source_field": "claim_boundary",
        "source_value": "no PDE regularity or blowup claim",
        "source_status": "FAIL_CLOSED_BOUNDARY",
        "symbol_level_role": "keeps Clay and PDE promotion flags false",
    },
)

CONTROL_CARD = {
    "O": "Sprint163 lane 2 owns the source-bound Sanni 2025 protocols.io symbol obstruction artifact.",
    "R": "Encode source metadata and scope only; do not promote any finite-dimensional symbol row into a PDE theorem.",
    "C": "One Python stdlib emitter writes normalized summary, rows, CSV, Markdown, and manifest artifacts.",
    "S": "The source is finite-dimensional and symbol-level only, with no PDE regularity or blowup assertion.",
    "L": "protocol metadata -> symbolic obstruction ledger -> fail-closed Clay/PDE promotion boundary.",
    "P": "Use this artifact as source evidence for obstruction naming, not as analytic Navier-Stokes proof evidence.",
    "G": "Validation passes only when source rows are present and every Clay/PDE promotion flag is false.",
    "F": "No Clay Navier-Stokes, PDE regularity, or blowup claim is supplied by this lane.",
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", "--output-dir", dest="out_dir", type=Path, default=OUT_DIR_DEFAULT)
    parser.add_argument(
        "--generated-at",
        default=None,
        help="ISO-8601 timestamp to place in generated_at; defaults to current UTC time.",
    )
    return parser.parse_args()


def stable_hash(value: Any) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def false_promotion_flags() -> dict[str, bool]:
    return {flag: False for flag in CLAY_PDE_PROMOTION_FLAGS}


def build_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for source in SOURCE_ROWS:
        row: dict[str, Any] = {
            **source,
            "sprint": SPRINT,
            "lane": LANE,
            "contract": CONTRACT,
            "protocol_title": PROTOCOL_TITLE,
            "protocol_author": PROTOCOL_AUTHOR,
            "protocol_doi_url": PROTOCOL_DOI_URL,
            "protocol_created_iso": PROTOCOL_CREATED,
            "protocol_modified_iso": PROTOCOL_MODIFIED,
            "finite_dimensional_symbol_level_only": True,
            "pde_regular_or_blowup_claim": False,
            "source_row_present": True,
        }
        row.update(false_promotion_flags())
        row["row_hash"] = stable_hash({key: value for key, value in row.items() if key != "row_hash"})
        rows.append(row)
    return rows


def promotion_flags_false(records: list[dict[str, Any]] | dict[str, Any]) -> bool:
    if isinstance(records, dict):
        return all(records.get(flag) is False for flag in CLAY_PDE_PROMOTION_FLAGS)
    return all(all(record.get(flag) is False for flag in CLAY_PDE_PROMOTION_FLAGS) for record in records)


def build_summary(repo_root: Path, out_dir: Path, generated_at: str) -> dict[str, Any]:
    rows = build_rows()
    source_fields_present = {row["source_field"] for row in rows}
    required_source_fields = {"title", "doi_url", "created", "modified", "scope", "claim_boundary"}
    source_rows_present = len(rows) == len(SOURCE_ROWS) and required_source_fields <= source_fields_present
    symbol_scope_only = all(row["finite_dimensional_symbol_level_only"] is True for row in rows)
    no_pde_claim = all(row["pde_regular_or_blowup_claim"] is False for row in rows)
    row_promotion_flags_false = promotion_flags_false(rows)

    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "generated_at": generated_at,
        "repo_root": str(repo_root),
        "out_dir": str(out_dir),
        "summary_path": str(out_dir / SUMMARY_NAME),
        "surface_name": "SanniSymbolObstructionSource",
        "TopologicalAlignmentObstruction": True,
        "TopologicalAlignmentObstruction_source_bound_only": True,
        "CriticalAlignmentTopologicalExhaustion": False,
        "BlowupImpliesSigmaConcentration": False,
        "SigmaConcentrationImpossible": False,
        "MechanismExhaustionForFullClayNS": False,
        "decision": "sanni_symbol_obstruction_source_fail_closed",
        "source_metadata": {
            "title": PROTOCOL_TITLE,
            "author": PROTOCOL_AUTHOR,
            "doi_url": PROTOCOL_DOI_URL,
            "created": PROTOCOL_CREATED_LABEL,
            "modified": PROTOCOL_MODIFIED_LABEL,
            "created_iso": PROTOCOL_CREATED,
            "modified_iso": PROTOCOL_MODIFIED,
            "source_kind": "protocols.io",
            "source_binding": "metadata_only",
        },
        "source_rows": rows,
        "source_row_count": len(rows),
        "required_source_fields": sorted(required_source_fields),
        "source_rows_present": source_rows_present,
        "finite_dimensional_symbol_level_only": symbol_scope_only,
        "pde_regular_or_blowup_claim": False,
        "no_pde_regular_or_blowup_claim": no_pde_claim,
        "row_authority_flags_false": row_promotion_flags_false,
        "control_card": CONTROL_CARD,
    }
    summary.update(false_promotion_flags())
    summary["summary_authority_flags_false"] = promotion_flags_false(summary)
    summary["validation_passed"] = (
        summary["source_rows_present"]
        and summary["finite_dimensional_symbol_level_only"]
        and summary["no_pde_regular_or_blowup_claim"]
        and summary["row_authority_flags_false"]
        and summary["summary_authority_flags_false"]
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
    metadata = summary["source_metadata"]
    lines = [
        "# Sprint 163 Sanni Symbol Obstruction Source",
        "",
        f"- Decision: `{summary['decision']}`",
        f"- Title: `{metadata['title']}`",
        f"- Author: `{metadata['author']}`",
        f"- DOI URL: `{metadata['doi_url']}`",
        f"- Created: `{metadata['created']}`",
        f"- Modified: `{metadata['modified']}`",
        f"- Finite-dimensional symbol-level only: `{summary['finite_dimensional_symbol_level_only']}`",
        f"- PDE regularity or blowup claim: `{summary['pde_regular_or_blowup_claim']}`",
        f"- Validation passed: `{summary['validation_passed']}`",
        "",
        "| row_id | source_field | source_status | source_value |",
        "| --- | --- | --- | --- |",
    ]
    for row in summary["source_rows"]:
        lines.append(
            f"| {row['row_id']} | {row['source_field']} | {row['source_status']} | {row['source_value']} |"
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
        write_json(temp_dir / ROWS_JSON_NAME, summary["source_rows"])
        write_csv(temp_dir / ROWS_CSV_NAME, summary["source_rows"])
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
