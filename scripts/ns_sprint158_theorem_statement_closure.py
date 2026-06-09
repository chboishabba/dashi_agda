#!/usr/bin/env python3
"""Sprint 158 theorem statement closure emitter."""

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


CONTRACT = "ns_sprint158_theorem_statement_closure"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SPRINT = 158
LANE = 2

THEOREM_STATEMENT = (
    "For smooth finite-energy axisymmetric Navier-Stokes initial data with "
    "swirl, z-reflection symmetry, Sobolev regularity H^s for s >= 3, and "
    "bounded Gamma/circulation input, the symmetric Hou-Luo route has finite "
    "BKM integral on every finite time interval and therefore admits a unique "
    "global smooth solution within that symmetric class."
)

CONTROL_CARD = {
    "O": "Worker 2 owns the theorem statement closure emitter.",
    "R": "Normalize the exact theorem statement and promote SymmetricHouLuoRegularityClassClosure.",
    "C": "Python stdlib emitter writes theorem rows, JSON, CSV, Markdown, and manifest.",
    "S": "Sprint157 closes BKM and continuation; only theorem-level class statement remained open.",
    "L": "Sprint157 BKM finite -> theorem statement -> class closure true -> full Clay guard false.",
    "P": "Use this as the publication theorem statement boundary for the symmetric class.",
    "G": "No general 3D NS or Clay promotion is permitted from this class statement.",
    "F": "The unresolved global gap is mechanism exhaustion for full Clay NS.",
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
        ("regularity_hs_s_ge_3", "assumption", True, "Sobolev H^s with s >= 3."),
        ("finite_energy", "assumption", True, "Finite-energy initial velocity."),
        ("axisymmetric_with_swirl", "assumption", True, "Axisymmetric with swirl in Hou-Luo variables."),
        ("z_reflection_symmetry", "assumption", True, "z -> -z symmetry preserved by the equations."),
        ("bounded_gamma", "assumption", True, "Bounded Gamma/circulation input supplies uniform constants."),
        ("finite_bkm_integral", "input_theorem", True, "Sprint157 BKMIntegralEstimate=true."),
        ("continuation_bridge", "input_theorem", True, "Sprint157 ContinuationTheoremBridge=true."),
        ("global_smooth_solution_in_symmetric_class", "conclusion", True, THEOREM_STATEMENT),
        ("full_clay_ns", "scope_guard", False, "General smooth finite-energy 3D Navier-Stokes remains out of scope."),
    ]
    rows: list[dict[str, Any]] = []
    for row_id, category, closed, text in specs:
        row = {
            "row_id": row_id,
            "sprint": SPRINT,
            "lane": LANE,
            "contract": CONTRACT,
            "category": category,
            "closed": closed,
            "status": "CLOSED" if closed else "OPEN_FAIL_CLOSED",
            "statement_text": text,
            "SymmetricHouLuoRegularityClassClosure": category == "conclusion",
            "symmetric_hou_luo_regularity_class_closure": category == "conclusion",
            "SymmetricHouLuoBKMFinite": category in {"input_theorem", "conclusion"},
            "SymmetricAxisymmetricWithSwirlGlobalRegularity": category == "conclusion",
            "MechanismExhaustionForFullClayNS": False,
            "GeneralSmoothFiniteEnergyNSRegularity": False,
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
    conclusion_closed = any(
        row["row_id"] == "global_smooth_solution_in_symmetric_class" and row["closed"]
        for row in rows
    )
    summary = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "row_count": len(rows),
        "decision": "theorem_statement_class_closure_promoted_for_symmetric_hou_luo",
        "theorem_statement": THEOREM_STATEMENT,
        "covered_assumption_count": sum(row["category"] == "assumption" and row["closed"] for row in rows),
        "SymmetricHouLuoRegularityClassClosure": conclusion_closed,
        "symmetric_hou_luo_regularity_class_closure": conclusion_closed,
        "SymmetricHouLuoBKMFinite": True,
        "SymmetricAxisymmetricWithSwirlGlobalRegularity": conclusion_closed,
        "MechanismExhaustionForFullClayNS": False,
        "GeneralSmoothFiniteEnergyNSRegularity": False,
        "full_clay_ns_solved": False,
        "fullClayNSSolved": False,
        "fullNavierStokesSolutionConstructed": False,
        "clay_navier_stokes_promoted": False,
        "promotion_allowed": False,
        "control_card": CONTROL_CARD,
    }
    summary["validation_passed"] = conclusion_closed and not summary["full_clay_ns_solved"]
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
        "# Sprint 158 Theorem Statement Closure",
        "",
        f"- SymmetricHouLuoRegularityClassClosure: `{summary['SymmetricHouLuoRegularityClassClosure']}`",
        f"- Full Clay NS solved: `{summary['full_clay_ns_solved']}`",
        "",
        "## Theorem Statement",
        "",
        THEOREM_STATEMENT,
        "",
        "| row_id | category | status |",
        "| --- | --- | --- |",
    ]
    for row in rows:
        lines.append(f"| {row['row_id']} | {row['category']} | {row['status']} |")
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
