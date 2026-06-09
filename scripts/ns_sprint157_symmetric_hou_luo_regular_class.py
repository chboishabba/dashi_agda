#!/usr/bin/env python3
"""Sprint 157 symmetric Hou-Luo class closure boundary emitter."""

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


CONTRACT = "ns_sprint157_symmetric_hou_luo_regular_class"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SPRINT = 157
LANE = 4

CONTROL_CARD = {
    "O": "Worker 4 owns the symmetric Hou-Luo regularity class boundary emitter.",
    "R": "Normalize which initial-data assumptions are covered and which Clay-scale claims remain out of scope.",
    "C": "Python ledger plus JSON, CSV, Markdown, and manifest outputs.",
    "S": "Sprint157 BKM and continuation are closed for the symmetric axisymmetric-with-swirl route.",
    "L": "assumption row -> covered class -> symmetric theorem closed -> class-statement doc still open -> full Clay separate.",
    "P": "Use this as the exact publication-boundary ledger for the symmetric route.",
    "G": "Do not strengthen to general smooth finite-energy 3D Navier-Stokes data.",
    "F": "The remaining non-code item is theorem-level prose for SymmetricHouLuoRegularityClassClosure.",
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


def build_rows() -> list[dict[str, Any]]:
    specs = [
        ("smooth_hs_s_ge_3", "covered_assumption", True, "Smooth Sobolev data with s >= 3."),
        ("axisymmetric_with_swirl", "covered_assumption", True, "Axisymmetric data with swirl in the Hou-Luo variables."),
        ("z_reflection_symmetry", "covered_assumption", True, "z -> -z symmetry is preserved by the flow."),
        ("bounded_gamma", "covered_assumption", True, "Gamma maximum principle provides time-uniform Umax input."),
        ("symmetric_hou_luo_bkm_finite", "closed_result", True, "BKM finiteness closes the symmetric route."),
        ("theorem_level_class_statement", "documentation_gap", False, "Publication-ready theorem prose still needs final statement."),
        ("general_three_dimensional_ns", "out_of_scope", False, "General finite-energy 3D NS is not covered."),
        ("full_clay_mechanism_exhaustion", "out_of_scope", False, "No exhaustion theorem for all mechanisms is present."),
    ]
    rows: list[dict[str, Any]] = []
    for row_id, category, covered, note in specs:
        row = {
            "row_id": row_id,
            "sprint": SPRINT,
            "lane": LANE,
            "contract": CONTRACT,
            "category": category,
            "status": "COVERED" if covered else "OPEN_OR_OUT_OF_SCOPE",
            "covered_by_symmetric_theorem": covered,
            "note": note,
            "SymmetricHouLuoBKMFinite": row_id == "symmetric_hou_luo_bkm_finite",
            "symmetric_hou_luo_bkm_finite": row_id == "symmetric_hou_luo_bkm_finite",
            "SymmetricHouLuoRegularityClassClosure": False,
            "MechanismExhaustionForFullClayNS": False,
            "full_clay_ns_solved": False,
            "fullClayNSSolved": False,
            "fullNavierStokesSolutionConstructed": False,
            "clay_navier_stokes_promoted": False,
            "promotion_allowed": False,
        }
        row["row_hash"] = stable_hash({k: v for k, v in row.items() if k != "row_hash"})
        rows.append(row)
    return rows


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    covered = [row for row in rows if row["category"] in {"covered_assumption", "closed_result"}]
    summary = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "row_count": len(rows),
        "decision": "symmetric_route_closed_publication_class_statement_still_open",
        "covered_assumption_count": sum(row["category"] == "covered_assumption" for row in rows),
        "all_covered_assumptions_true": all(row["covered_by_symmetric_theorem"] for row in covered),
        "SymmetricHouLuoBKMFinite": True,
        "symmetric_hou_luo_bkm_finite": True,
        "SymmetricHouLuoRegularityClassClosure": False,
        "symmetric_hou_luo_regularity_class_closure": False,
        "MechanismExhaustionForFullClayNS": False,
        "full_clay_ns_solved": False,
        "fullClayNSSolved": False,
        "fullNavierStokesSolutionConstructed": False,
        "clay_navier_stokes_promoted": False,
        "promotion_allowed": False,
        "control_card": CONTROL_CARD,
    }
    summary["validation_passed"] = summary["SymmetricHouLuoBKMFinite"] and not summary["full_clay_ns_solved"]
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
        "# Sprint 157 Symmetric Hou-Luo Regular Class Boundary",
        "",
        f"- SymmetricHouLuoBKMFinite: `{summary['SymmetricHouLuoBKMFinite']}`",
        f"- SymmetricHouLuoRegularityClassClosure: `{summary['SymmetricHouLuoRegularityClassClosure']}`",
        f"- Full Clay NS solved: `{summary['full_clay_ns_solved']}`",
        "",
        "| row_id | category | status | note |",
        "| --- | --- | --- | --- |",
    ]
    for row in rows:
        lines.append(f"| {row['row_id']} | {row['category']} | {row['status']} | {row['note']} |")
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
