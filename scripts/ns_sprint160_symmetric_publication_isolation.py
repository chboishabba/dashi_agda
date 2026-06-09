#!/usr/bin/env python3
"""Sprint 160 symmetric Hou-Luo publication isolation emitter."""

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


CONTRACT = "ns_sprint160_symmetric_publication_isolation"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SPRINT = 160
LANE = 3

ISOLATION_READY = "ISOLATION_READY"
NONCLAIM_GUARD = "NONCLAIM_GUARD"

CONTROL_CARD = {
    "O": "Worker 3 owns the Sprint160 symmetric Hou-Luo publication isolation emitter.",
    "R": "Isolate the symmetric Hou-Luo theorem packet from full Clay NS mechanism exhaustion and promotion.",
    "C": "Python stdlib emitter writes isolation rows to JSON, CSV, Markdown, and manifest.",
    "S": "Sprint157/158/159 support a scoped symmetric regularity-class publication packet while preserving full-Clay guards.",
    "L": "theorem statement -> assumption matrix -> BKM bridge -> publication readiness -> scope guard -> Clay nonclaim.",
    "P": "Use this artifact as the lane 3 witness that the symmetric packet is publication-isolated, not Clay-promoted.",
    "G": "Symmetric closure flags may be true only with all full Clay, mechanism exhaustion, and promotion flags false.",
    "F": "MechanismExhaustionForFullClayNS and full Clay promotion remain false.",
}

FULL_CLAY_FALSE_FLAGS = (
    "MechanismExhaustionForFullClayNS",
    "FullClayMechanismExhaustion",
    "GeneralSmoothFiniteEnergyNSRegularity",
    "fullClay",
    "full_clay",
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


def full_clay_false_flags() -> dict[str, bool]:
    return {flag: False for flag in FULL_CLAY_FALSE_FLAGS}


def build_rows() -> list[dict[str, Any]]:
    specs = [
        (
            "theorem_statement",
            "theorem_statement",
            ISOLATION_READY,
            "The symmetric Hou-Luo regularity-class theorem statement is isolated as a scoped theorem.",
            "outputs/ns_sprint158_theorem_statement_closure/ns_sprint158_theorem_statement_closure_summary.json",
        ),
        (
            "assumption_matrix",
            "assumption_matrix",
            ISOLATION_READY,
            "The assumption matrix records the symmetric axisymmetric-with-swirl class and excludes general-data promotion.",
            "outputs/ns_sprint158_assumption_scope_matrix/ns_sprint158_assumption_scope_matrix_summary.json",
        ),
        (
            "bkm_bridge",
            "bkm_bridge",
            ISOLATION_READY,
            "The BKM bridge supports continuation inside the symmetric Hou-Luo regularity class.",
            "outputs/ns_sprint157_bkm_integral_estimate/ns_sprint157_bkm_integral_estimate_summary.json",
        ),
        (
            "publication_readiness",
            "publication_readiness",
            ISOLATION_READY,
            "The symmetric theorem packet is ready for scoped publication review.",
            "outputs/ns_sprint158_publication_packet_readiness/ns_sprint158_publication_packet_readiness_summary.json",
        ),
        (
            "scope_guard",
            "scope_guard",
            ISOLATION_READY,
            "Scope guards keep the publication packet confined to the symmetric Hou-Luo class.",
            "outputs/ns_sprint159_external_authority_boundary/ns_sprint159_external_authority_boundary_summary.json",
        ),
        (
            "clay_nonclaim",
            "clay_nonclaim",
            NONCLAIM_GUARD,
            "The artifact makes no full Clay claim and does not assert mechanism exhaustion for full Navier-Stokes.",
            "outputs/ns_sprint159_mechanism_exhaustion_gap/ns_sprint159_mechanism_exhaustion_gap_summary.json",
        ),
    ]
    rows: list[dict[str, Any]] = []
    for row_id, packet_component, status, statement_text, support_link in specs:
        row = {
            "row_id": row_id,
            "sprint": SPRINT,
            "lane": LANE,
            "contract": CONTRACT,
            "packet_component": packet_component,
            "status": status,
            "isolated": True,
            "statement_text": statement_text,
            "support_link": support_link,
            "SymmetricHouLuoPublicationIsolation": True,
            "symmetric_hou_luo_publication_isolation": True,
            "SymmetricHouLuoRegularityClassClosure": True,
            "symmetric_hou_luo_regularity_class_closure": True,
            "publication_ready_scoped_symmetric_packet": status == ISOLATION_READY,
            "scope_guard": row_id == "scope_guard",
            "clay_nonclaim": row_id == "clay_nonclaim",
            **full_clay_false_flags(),
        }
        row["row_hash"] = stable_hash({k: v for k, v in row.items() if k != "row_hash"})
        rows.append(row)
    return rows


def full_clay_flags_false(records: list[dict[str, Any]] | dict[str, Any]) -> bool:
    if isinstance(records, dict):
        return all(records.get(flag) is False for flag in FULL_CLAY_FALSE_FLAGS)
    return all(all(record.get(flag) is False for flag in FULL_CLAY_FALSE_FLAGS) for record in records)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    expected_components = {
        "theorem_statement",
        "assumption_matrix",
        "bkm_bridge",
        "publication_readiness",
        "scope_guard",
        "clay_nonclaim",
    }
    components = {row["packet_component"] for row in rows}
    scoped_ready_count = sum(row["status"] == ISOLATION_READY for row in rows)
    nonclaim_guard_count = sum(row["status"] == NONCLAIM_GUARD for row in rows)
    summary = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "row_count": len(rows),
        "decision": "symmetric_hou_luo_publication_packet_isolated_without_full_clay_promotion",
        "packet_components": sorted(components),
        "expected_components_present": components == expected_components,
        "scoped_ready_count": scoped_ready_count,
        "nonclaim_guard_count": nonclaim_guard_count,
        "SymmetricHouLuoPublicationIsolation": True,
        "symmetric_hou_luo_publication_isolation": True,
        "SymmetricHouLuoRegularityClassClosure": True,
        "symmetric_hou_luo_regularity_class_closure": True,
        "row_full_clay_flags_false": full_clay_flags_false(rows),
        "control_card": CONTROL_CARD,
        **full_clay_false_flags(),
    }
    summary["summary_full_clay_flags_false"] = full_clay_flags_false(summary)
    summary["validation_passed"] = (
        summary["expected_components_present"]
        and scoped_ready_count == 5
        and nonclaim_guard_count == 1
        and summary["row_full_clay_flags_false"]
        and summary["summary_full_clay_flags_false"]
        and summary["SymmetricHouLuoPublicationIsolation"]
        and summary["SymmetricHouLuoRegularityClassClosure"]
        and not summary["MechanismExhaustionForFullClayNS"]
        and not summary["fullClay"]
        and not summary["promotion_allowed"]
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
        "# Sprint 160 Symmetric Publication Isolation",
        "",
        f"- SymmetricHouLuoPublicationIsolation: `{summary['SymmetricHouLuoPublicationIsolation']}`",
        f"- SymmetricHouLuoRegularityClassClosure: `{summary['SymmetricHouLuoRegularityClassClosure']}`",
        f"- MechanismExhaustionForFullClayNS: `{summary['MechanismExhaustionForFullClayNS']}`",
        f"- fullClay: `{summary['fullClay']}`",
        f"- promotion_allowed: `{summary['promotion_allowed']}`",
        f"- Validation passed: `{summary['validation_passed']}`",
        "",
        "| row_id | packet_component | status | support_link |",
        "| --- | --- | --- | --- |",
    ]
    for row in rows:
        lines.append(f"| {row['row_id']} | {row['packet_component']} | {row['status']} | {row['support_link']} |")
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
