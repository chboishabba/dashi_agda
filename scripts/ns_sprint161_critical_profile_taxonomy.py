#!/usr/bin/env python3
"""Sprint 161 critical-profile taxonomy emitter."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import shutil
import sys
import tempfile
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint161_critical_profile_taxonomy"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SPRINT = 161
LANE = 4

KNOWN_CLOSED = "KNOWN_CLOSED"
SYMMETRIC_CLOSED = "SYMMETRIC_CLOSED"
OPEN = "OPEN"

PROFILE_CLASSES = (
    "zero",
    "Type-I self-similar",
    "axisymmetric no swirl",
    "axisymmetric with swirl Gamma-bounded/symmetric",
    "non-axisymmetric Type-I",
    "non-axisymmetric Type-II",
    "discretely self-similar",
    "ancient bounded non-symmetric",
)

FULL_CLAY_FALSE_FLAGS = (
    "MechanismExhaustionForFullClayNS",
    "FullClayMechanismExhaustion",
    "GeneralSmoothFiniteEnergyNSRegularity",
    "full_clay",
    "fullClay",
    "full_clay_ns_solved",
    "fullClayNSSolved",
    "fullNavierStokesSolutionConstructed",
    "clay_navier_stokes_promoted",
    "clayNavierStokesPromoted",
    "promotion_allowed",
    "promotionAllowed",
    "ClaySubmissionReady",
    "ClaySubmissionPromotionPacket",
    "FullClay",
)

CONTROL_CARD = {
    "O": "Worker 4 owns the Sprint161 critical-profile taxonomy emitter.",
    "R": "Separate closed profile classes from open critical-profile classes without promoting full Clay NS.",
    "C": "Python stdlib emitter writes normalized rows, summary, CSV, Markdown, and manifest.",
    "S": "Sprint160 governance keeps full Clay false while scoped symmetric classes may be isolated as closed.",
    "L": "profile class -> closure group -> evidence boundary -> Full Clay false guard.",
    "P": "Use this artifact as the lane 4 taxonomy for critical-profile accounting.",
    "G": "Validation requires exactly eight profile classes, closed/open separation, and every Full Clay flag false.",
    "F": "Open non-symmetric and Type-II/DSS profile classes remain non-exhausted for full Clay.",
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def stable_hash(value: Any) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(payload).hexdigest()


def file_sha256(path: Path) -> str | None:
    if not path.exists():
        return None
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def full_clay_false_flags() -> dict[str, bool]:
    return {flag: False for flag in FULL_CLAY_FALSE_FLAGS}


def build_rows() -> list[dict[str, Any]]:
    specs = [
        {
            "profile_id": "zero",
            "profile_class": "zero",
            "closure_group": KNOWN_CLOSED,
            "row_kind": "known_closed",
            "taxonomy_status": "closed_known_trivial_profile",
            "symmetric_class": True,
            "known_closed": True,
            "symmetric_closed": False,
            "open_row": False,
            "closure_note": "Zero profile is the closed trivial critical profile.",
            "evidence_boundary": "trivial_zero_profile",
        },
        {
            "profile_id": "type_i_self_similar",
            "profile_class": "Type-I self-similar",
            "closure_group": KNOWN_CLOSED,
            "row_kind": "known_closed",
            "taxonomy_status": "closed_known_type_i_self_similar_obstruction",
            "symmetric_class": False,
            "known_closed": True,
            "symmetric_closed": False,
            "open_row": False,
            "closure_note": "Continuous Type-I self-similar blowup profiles are treated as a known closed obstruction class, not as full-profile exhaustion.",
            "evidence_boundary": "type_i_self_similar_nonexistence_boundary",
        },
        {
            "profile_id": "axisymmetric_no_swirl",
            "profile_class": "axisymmetric no swirl",
            "closure_group": SYMMETRIC_CLOSED,
            "row_kind": "symmetric_closed",
            "taxonomy_status": "closed_symmetric_no_swirl_regular_class",
            "symmetric_class": True,
            "known_closed": False,
            "symmetric_closed": True,
            "open_row": False,
            "closure_note": "Axisymmetric no-swirl data sit in a closed symmetric regularity class.",
            "evidence_boundary": "axisymmetric_no_swirl_regular_class",
        },
        {
            "profile_id": "axisymmetric_with_swirl_gamma_bounded_symmetric",
            "profile_class": "axisymmetric with swirl Gamma-bounded/symmetric",
            "closure_group": SYMMETRIC_CLOSED,
            "row_kind": "symmetric_closed",
            "taxonomy_status": "closed_symmetric_gamma_bounded_swirl_class",
            "symmetric_class": True,
            "known_closed": False,
            "symmetric_closed": True,
            "open_row": False,
            "closure_note": "Gamma-bounded symmetric axisymmetric-with-swirl profiles are scoped symmetric closed rows.",
            "evidence_boundary": "symmetric_hou_luo_gamma_bounded_scope",
        },
        {
            "profile_id": "non_axisymmetric_type_i",
            "profile_class": "non-axisymmetric Type-I",
            "closure_group": OPEN,
            "row_kind": "open",
            "taxonomy_status": "open_non_axisymmetric_type_i_profile_class",
            "symmetric_class": False,
            "known_closed": False,
            "symmetric_closed": False,
            "open_row": True,
            "closure_note": "Non-axisymmetric Type-I profiles remain open in this taxonomy.",
            "evidence_boundary": "non_axisymmetric_type_i_gap",
        },
        {
            "profile_id": "non_axisymmetric_type_ii",
            "profile_class": "non-axisymmetric Type-II",
            "closure_group": OPEN,
            "row_kind": "open",
            "taxonomy_status": "open_non_axisymmetric_type_ii_profile_class",
            "symmetric_class": False,
            "known_closed": False,
            "symmetric_closed": False,
            "open_row": True,
            "closure_note": "Non-axisymmetric Type-II profiles remain open and are not exhausted by symmetric closure.",
            "evidence_boundary": "non_axisymmetric_type_ii_gap",
        },
        {
            "profile_id": "discretely_self_similar",
            "profile_class": "discretely self-similar",
            "closure_group": OPEN,
            "row_kind": "open",
            "taxonomy_status": "open_discrete_self_similarity_profile_class",
            "symmetric_class": False,
            "known_closed": False,
            "symmetric_closed": False,
            "open_row": True,
            "closure_note": "Discretely self-similar profiles remain open in the critical-profile taxonomy.",
            "evidence_boundary": "discrete_self_similarity_gap",
        },
        {
            "profile_id": "ancient_bounded_non_symmetric",
            "profile_class": "ancient bounded non-symmetric",
            "closure_group": OPEN,
            "row_kind": "open",
            "taxonomy_status": "open_ancient_bounded_non_symmetric_profile_class",
            "symmetric_class": False,
            "known_closed": False,
            "symmetric_closed": False,
            "open_row": True,
            "closure_note": "Ancient bounded non-symmetric profiles remain open and block profile-exhaustion promotion.",
            "evidence_boundary": "ancient_bounded_non_symmetric_gap",
        },
    ]
    rows: list[dict[str, Any]] = []
    for ordinal, spec in enumerate(specs, start=1):
        row = {
            "ordinal": ordinal,
            "sprint": SPRINT,
            "lane": LANE,
            "contract": CONTRACT,
            "FullClay": False,
            "full_clay_boundary": "false_guard",
            "profile_exhaustion_for_full_clay": False,
            "profile_taxonomy_complete_as_inventory": True,
            **spec,
            **full_clay_false_flags(),
        }
        row["row_hash"] = stable_hash({k: v for k, v in row.items() if k != "row_hash"})
        rows.append(row)
    return rows


def full_clay_flags_false(records: list[dict[str, Any]] | dict[str, Any]) -> bool:
    if isinstance(records, dict):
        return all(records.get(flag) is False for flag in FULL_CLAY_FALSE_FLAGS)
    return all(all(record.get(flag) is False for flag in FULL_CLAY_FALSE_FLAGS) for record in records)


def validate_rows(rows: list[dict[str, Any]]) -> dict[str, Any]:
    classes = [row["profile_class"] for row in rows]
    class_set = set(classes)
    known_closed = [row for row in rows if row["closure_group"] == KNOWN_CLOSED]
    symmetric_closed = [row for row in rows if row["closure_group"] == SYMMETRIC_CLOSED]
    open_rows = [row for row in rows if row["closure_group"] == OPEN]
    closed_rows = [row for row in rows if not row["open_row"]]
    closed_open_consistent = all(
        (row["closure_group"] == OPEN) == row["open_row"]
        and row["known_closed"] == (row["closure_group"] == KNOWN_CLOSED)
        and row["symmetric_closed"] == (row["closure_group"] == SYMMETRIC_CLOSED)
        for row in rows
    )
    no_full_clay_profile_exhaustion = all(row["profile_exhaustion_for_full_clay"] is False for row in rows)
    return {
        "expected_profile_classes": list(PROFILE_CLASSES),
        "profile_classes": classes,
        "profile_class_set_exact": class_set == set(PROFILE_CLASSES) and len(classes) == len(PROFILE_CLASSES),
        "known_closed_count": len(known_closed),
        "symmetric_closed_count": len(symmetric_closed),
        "closed_count": len(closed_rows),
        "open_count": len(open_rows),
        "closed_profile_ids": [row["profile_id"] for row in closed_rows],
        "open_profile_ids": [row["profile_id"] for row in open_rows],
        "closed_open_consistent": closed_open_consistent,
        "row_full_clay_flags_false": full_clay_flags_false(rows),
        "no_full_clay_profile_exhaustion": no_full_clay_profile_exhaustion,
    }


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    validation = validate_rows(rows)
    summary = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "row_count": len(rows),
        "decision": "critical_profile_taxonomy_inventory_with_closed_rows_separated_from_open_rows",
        "closure_groups": {
            KNOWN_CLOSED: validation["known_closed_count"],
            SYMMETRIC_CLOSED: validation["symmetric_closed_count"],
            OPEN: validation["open_count"],
        },
        "closed_profile_ids": validation["closed_profile_ids"],
        "open_profile_ids": validation["open_profile_ids"],
        "FullClay": False,
        "full_clay": False,
        "profile_exhaustion_for_full_clay": False,
        "profile_taxonomy_complete_as_inventory": True,
        "control_card": CONTROL_CARD,
        **full_clay_false_flags(),
        "validation": validation,
    }
    summary["summary_full_clay_flags_false"] = full_clay_flags_false(summary)
    summary["validation_passed"] = (
        len(rows) == 8
        and validation["profile_class_set_exact"]
        and validation["known_closed_count"] == 2
        and validation["symmetric_closed_count"] == 2
        and validation["closed_count"] == 4
        and validation["open_count"] == 4
        and validation["closed_open_consistent"]
        and validation["row_full_clay_flags_false"]
        and validation["no_full_clay_profile_exhaustion"]
        and summary["summary_full_clay_flags_false"]
        and summary["FullClay"] is False
        and summary["full_clay"] is False
        and summary["profile_exhaustion_for_full_clay"] is False
    )
    summary["summary_hash"] = stable_hash({k: v for k, v in summary.items() if k != "summary_hash"})
    return summary


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def render_markdown(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# Sprint 161 Critical Profile Taxonomy",
        "",
        f"- Decision: `{summary['decision']}`",
        f"- Row count: `{summary['row_count']}`",
        f"- Known closed rows: `{summary['closure_groups'][KNOWN_CLOSED]}`",
        f"- Symmetric closed rows: `{summary['closure_groups'][SYMMETRIC_CLOSED]}`",
        f"- Open rows: `{summary['closure_groups'][OPEN]}`",
        f"- FullClay: `{summary['FullClay']}`",
        f"- Profile exhaustion for full Clay: `{summary['profile_exhaustion_for_full_clay']}`",
        f"- Validation passed: `{summary['validation_passed']}`",
        "",
        "## Closed Rows",
        "",
        "| profile_id | profile_class | closure_group | taxonomy_status |",
        "| --- | --- | --- | --- |",
    ]
    for row in rows:
        if not row["open_row"]:
            lines.append(
                f"| {row['profile_id']} | {row['profile_class']} | {row['closure_group']} | {row['taxonomy_status']} |"
            )
    lines.extend(
        [
            "",
            "## Open Rows",
            "",
            "| profile_id | profile_class | closure_group | taxonomy_status |",
            "| --- | --- | --- | --- |",
        ]
    )
    for row in rows:
        if row["open_row"]:
            lines.append(
                f"| {row['profile_id']} | {row['profile_class']} | {row['closure_group']} | {row['taxonomy_status']} |"
            )
    lines.extend(["", "## O/R/C/S/L/P/G/F", ""])
    for key in ("O", "R", "C", "S", "L", "P", "G", "F"):
        lines.append(f"- {key}: {CONTROL_CARD[key]}")
    lines.append("")
    return "\n".join(lines)


def output_files(out_dir: Path) -> dict[str, Path]:
    return {
        "summary": out_dir / f"{CONTRACT}_summary.json",
        "rows_json": out_dir / f"{CONTRACT}_rows.json",
        "rows_csv": out_dir / f"{CONTRACT}_rows.csv",
        "markdown": out_dir / f"{CONTRACT}.md",
        "manifest": out_dir / f"{CONTRACT}_manifest.json",
    }


def build_manifest(out_dir: Path, summary: dict[str, Any]) -> dict[str, Any]:
    files = output_files(out_dir)
    manifest = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "validation_passed": summary["validation_passed"],
        "normalized_outputs": {
            "json": str(files["rows_json"]),
            "csv": str(files["rows_csv"]),
            "markdown": str(files["markdown"]),
            "manifest": str(files["manifest"]),
            "summary": str(files["summary"]),
        },
        "files": {
            key: {"path": str(path), "exists": path.exists(), "sha256": file_sha256(path)}
            for key, path in files.items()
        },
    }
    manifest["manifest_hash"] = stable_hash({k: v for k, v in manifest.items() if k != "manifest_hash"})
    return manifest


def write_outputs(repo_root: Path, out_dir: Path, rows: list[dict[str, Any]], summary: dict[str, Any]) -> None:
    final_out = out_dir if out_dir.is_absolute() else repo_root / out_dir
    final_out.parent.mkdir(parents=True, exist_ok=True)
    temp_dir = Path(tempfile.mkdtemp(prefix=f".{CONTRACT}.", dir=final_out.parent))
    try:
        files = output_files(temp_dir)
        write_json(files["rows_json"], rows)
        write_csv(files["rows_csv"], rows)
        write_json(files["summary"], summary)
        files["markdown"].write_text(render_markdown(summary, rows), encoding="utf-8")
        write_json(files["manifest"], build_manifest(temp_dir, summary))
        if final_out.exists():
            shutil.rmtree(final_out)
        os.replace(temp_dir, final_out)
        write_json(final_out / f"{CONTRACT}_manifest.json", build_manifest(final_out, summary))
    except Exception:
        shutil.rmtree(temp_dir, ignore_errors=True)
        raise


def main() -> int:
    args = parse_args()
    rows = build_rows()
    summary = build_summary(rows)
    write_outputs(args.repo_root.resolve(), args.out_dir, rows, summary)
    print(
        json.dumps(
            {
                "contract": CONTRACT,
                "validation_passed": summary["validation_passed"],
                "row_count": summary["row_count"],
                "out_dir": str(args.out_dir),
            },
            sort_keys=True,
        )
    )
    return 0 if summary["validation_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
