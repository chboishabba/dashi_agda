#!/usr/bin/env python3
"""Sprint 160 Clay governance rule emitter."""

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


CONTRACT = "ns_sprint160_clay_governance_rule"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SPRINT = 160
LANE = 2

RULE_TRUE = "RULE_TRUE"
EXTERNAL_AUTHORITY_BOUNDARY = "EXTERNAL_AUTHORITY_BOUNDARY"
PUBLISH_AND_ISOLATE = "PUBLISH_AND_ISOLATE"
NO_LOCAL_CLAY_SPRINT = "NO_LOCAL_CLAY_SPRINT"

CLAY_FLAGS = (
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
)

CONTROL_CARD = {
    "O": "Worker 2 owns the Sprint160 Clay governance rule emitter.",
    "R": "Encode the fail-closed rule that local Clay mechanism-exhaustion work cannot continue without new PDE math.",
    "C": "Python stdlib emitter writes governance rows to JSON, CSV, Markdown, summary, and manifest.",
    "S": "Sprint159 recorded mechanism-exhaustion gaps and external-authority boundaries after scoped symmetric Hou-Luo closure.",
    "L": "no new PDE math -> no more local Clay sprint -> full Clay boundary remains external -> symmetric result is isolated for publication.",
    "P": "Use this artifact as the Sprint160 lane 2 stop rule for local Clay-promotion attempts.",
    "G": "Validation passes only when the rule is true, no_more_local_sprint is true, and all Clay flags are false.",
    "F": "Full Clay remains outside local authority; symmetric Hou-Luo should be published or isolated as a scoped result.",
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def stable_hash(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def file_sha256(path: Path) -> str | None:
    if not path.exists():
        return None
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def clay_flag_fields() -> dict[str, bool]:
    return {flag: False for flag in CLAY_FLAGS}


def build_rows() -> list[dict[str, Any]]:
    specs = [
        {
            "row_id": "no_local_mechanism_exhaustion_sprint_without_new_pde_math",
            "category": NO_LOCAL_CLAY_SPRINT,
            "canonical_rule": "NoLocalClayMechanismSprintWithoutNewPDEMath",
            "rule_text": "No local Clay mechanism-exhaustion sprint may proceed without new PDE math.",
            "rule_true": True,
            "no_more_local_sprint": True,
            "new_pde_math_required": True,
            "new_pde_math_present": False,
            "full_clay_external_authority_boundary": True,
            "symmetric_hou_luo_publish_isolate": True,
            "governance_action": "stop_local_clay_mechanism_exhaustion_sprints",
            "support_links": [
                "outputs/ns_sprint159_mechanism_exhaustion_gap/ns_sprint159_mechanism_exhaustion_gap_summary.json",
                "outputs/ns_sprint159_criteria_inventory/ns_sprint159_criteria_inventory_summary.json",
            ],
        },
        {
            "row_id": "full_clay_remains_external_authority_boundary",
            "category": EXTERNAL_AUTHORITY_BOUNDARY,
            "canonical_rule": "NoLocalClayMechanismSprintWithoutNewPDEMath",
            "rule_text": "Full Clay Navier-Stokes remains an external-authority boundary.",
            "rule_true": True,
            "no_more_local_sprint": True,
            "new_pde_math_required": True,
            "new_pde_math_present": False,
            "full_clay_external_authority_boundary": True,
            "symmetric_hou_luo_publish_isolate": True,
            "governance_action": "keep_full_clay_external",
            "support_links": [
                "outputs/ns_sprint159_external_authority_boundary/ns_sprint159_external_authority_boundary_summary.json",
                "outputs/ns_sprint159_mechanism_exhaustion_gap/ns_sprint159_mechanism_exhaustion_gap_summary.json",
            ],
        },
        {
            "row_id": "symmetric_hou_luo_publish_or_isolate",
            "category": PUBLISH_AND_ISOLATE,
            "canonical_rule": "NoLocalClayMechanismSprintWithoutNewPDEMath",
            "rule_text": "The symmetric Hou-Luo result should be published or isolated as a scoped result.",
            "rule_true": True,
            "no_more_local_sprint": True,
            "new_pde_math_required": True,
            "new_pde_math_present": False,
            "full_clay_external_authority_boundary": True,
            "symmetric_hou_luo_publish_isolate": True,
            "governance_action": "publish_or_isolate_symmetric_hou_luo",
            "support_links": [
                "outputs/ns_sprint159_external_authority_boundary/ns_sprint159_external_authority_boundary_summary.json",
                "outputs/ns_sprint159_criteria_inventory/ns_sprint159_criteria_inventory_summary.json",
            ],
        },
    ]
    rows: list[dict[str, Any]] = []
    for spec in specs:
        row: dict[str, Any] = {
            **spec,
            "sprint": SPRINT,
            "lane": LANE,
            "contract": CONTRACT,
            "status": RULE_TRUE,
            "ExternalAuthorityBoundary": True,
            "external_authority_boundary": True,
            "SymmetricHouLuoRegularityClassClosure": spec["row_id"] == "symmetric_hou_luo_publish_or_isolate",
            "SymmetricHouLuoShouldBePublishedOrIsolated": spec["symmetric_hou_luo_publish_isolate"],
        }
        row.update(clay_flag_fields())
        row["row_hash"] = stable_hash({k: v for k, v in row.items() if k != "row_hash"})
        rows.append(row)
    return rows


def clay_flags_false(records: list[dict[str, Any]] | dict[str, Any]) -> bool:
    if isinstance(records, dict):
        return all(records.get(flag) is False for flag in CLAY_FLAGS)
    return all(all(record.get(flag) is False for flag in CLAY_FLAGS) for record in records)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    rule_true = all(row["rule_true"] is True and row["status"] == RULE_TRUE for row in rows)
    no_more_local_sprint = all(row["no_more_local_sprint"] is True for row in rows)
    full_clay_boundary = all(row["full_clay_external_authority_boundary"] is True for row in rows)
    symmetric_publish_isolate = all(row["symmetric_hou_luo_publish_isolate"] is True for row in rows)
    new_pde_math_absent = all(row["new_pde_math_present"] is False for row in rows)
    row_clay_flags_false = clay_flags_false(rows)
    summary = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "row_count": len(rows),
        "decision": "clay_governance_rule_fail_closed",
        "canonical_rule": "NoLocalClayMechanismSprintWithoutNewPDEMath",
        "rule_true": rule_true,
        "no_more_local_sprint": no_more_local_sprint,
        "new_pde_math_required": True,
        "new_pde_math_present": False,
        "new_pde_math_absent": new_pde_math_absent,
        "full_clay_external_authority_boundary": full_clay_boundary,
        "symmetric_hou_luo_publish_isolate": symmetric_publish_isolate,
        "row_clay_flags_false": row_clay_flags_false,
        "ExternalAuthorityBoundary": full_clay_boundary,
        "external_authority_boundary": full_clay_boundary,
        "SymmetricHouLuoShouldBePublishedOrIsolated": symmetric_publish_isolate,
        "control_card": CONTROL_CARD,
    }
    summary.update(clay_flag_fields())
    summary["summary_clay_flags_false"] = clay_flags_false(summary)
    summary["validation_passed"] = (
        len(rows) == 3
        and summary["rule_true"]
        and summary["no_more_local_sprint"]
        and summary["full_clay_external_authority_boundary"]
        and summary["symmetric_hou_luo_publish_isolate"]
        and summary["new_pde_math_absent"]
        and summary["row_clay_flags_false"]
        and summary["summary_clay_flags_false"]
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
        "# Sprint 160 Clay Governance Rule",
        "",
        f"- Decision: `{summary['decision']}`",
        f"- Canonical rule: `{summary['canonical_rule']}`",
        f"- Rule true: `{summary['rule_true']}`",
        f"- No more local sprint: `{summary['no_more_local_sprint']}`",
        f"- New PDE math present: `{summary['new_pde_math_present']}`",
        f"- Full Clay external authority boundary: `{summary['full_clay_external_authority_boundary']}`",
        f"- Symmetric Hou-Luo publish/isolate: `{summary['symmetric_hou_luo_publish_isolate']}`",
        f"- Clay flags false: `{summary['summary_clay_flags_false']}`",
        f"- Validation passed: `{summary['validation_passed']}`",
        "",
        "| row_id | category | status | governance_action |",
        "| --- | --- | --- | --- |",
    ]
    for row in rows:
        lines.append(f"| {row['row_id']} | {row['category']} | {row['status']} | {row['governance_action']} |")
    lines.extend(["", "## O/R/C/S/L/P/G/F", ""])
    for key in ("O", "R", "C", "S", "L", "P", "G", "F"):
        lines.append(f"- {key}: {CONTROL_CARD[key]}")
    lines.append("")
    return "\n".join(lines)


def build_manifest(out_dir: Path, summary: dict[str, Any]) -> dict[str, Any]:
    files = {
        "summary": out_dir / f"{CONTRACT}_summary.json",
        "rows_json": out_dir / f"{CONTRACT}_rows.json",
        "rows_csv": out_dir / f"{CONTRACT}_rows.csv",
        "markdown": out_dir / f"{CONTRACT}.md",
        "manifest": out_dir / f"{CONTRACT}_manifest.json",
    }
    manifest = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "validation_passed": summary["validation_passed"],
        "files": {key: {"path": str(path), "exists": path.exists(), "sha256": file_sha256(path)} for key, path in files.items()},
    }
    manifest["manifest_hash"] = stable_hash({k: v for k, v in manifest.items() if k != "manifest_hash"})
    return manifest


def write_outputs(repo_root: Path, out_dir: Path, rows: list[dict[str, Any]], summary: dict[str, Any]) -> None:
    final_out = out_dir if out_dir.is_absolute() else repo_root / out_dir
    final_out.parent.mkdir(parents=True, exist_ok=True)
    temp_dir = Path(tempfile.mkdtemp(prefix=f".{CONTRACT}.", dir=final_out.parent))
    try:
        write_json(temp_dir / f"{CONTRACT}_rows.json", rows)
        write_csv(temp_dir / f"{CONTRACT}_rows.csv", rows)
        write_json(temp_dir / f"{CONTRACT}_summary.json", summary)
        (temp_dir / f"{CONTRACT}.md").write_text(render_markdown(summary, rows), encoding="utf-8")
        write_json(temp_dir / f"{CONTRACT}_manifest.json", build_manifest(temp_dir, summary))
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
    print(json.dumps({"contract": CONTRACT, "validation_passed": summary["validation_passed"], "out_dir": str(args.out_dir)}, sort_keys=True))
    return 0 if summary["validation_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
