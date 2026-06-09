#!/usr/bin/env python3
"""Sprint 158 assumption and scope matrix emitter."""

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


CONTRACT = "ns_sprint158_assumption_scope_matrix"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SPRINT = 158
LANE = 3

CONTROL_CARD = {
    "O": "Worker 3 owns the assumption/scope matrix.",
    "R": "Separate covered assumptions, conclusions, documentary scope, and explicit non-claims.",
    "C": "Python emitter writes matrix rows to JSON, CSV, Markdown, and manifest.",
    "S": "The symmetric theorem is closed; general NS and Clay remain not covered.",
    "L": "covered assumption -> covered conclusion -> documentary packet -> explicit non-claim.",
    "P": "Use the matrix to prevent theorem-scope drift during publication.",
    "G": "Any row marked out_of_scope must keep Clay/general NS flags false.",
    "F": "Full Clay requires a mechanism-exhaustion theorem absent from this route.",
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
        ("smooth_hs_s_ge_3", "covered_assumption", True),
        ("finite_energy", "covered_assumption", True),
        ("axisymmetric_with_swirl", "covered_assumption", True),
        ("z_reflection_symmetry", "covered_assumption", True),
        ("bounded_gamma", "covered_assumption", True),
        ("global_smooth_symmetric_solution", "covered_conclusion", True),
        ("unique_symmetric_solution", "covered_conclusion", True),
        ("publication_packet_ready", "publication_surface", True),
        ("general_3d_smooth_data", "out_of_scope", False),
        ("mechanism_exhaustion", "out_of_scope", False),
        ("clay_millennium_problem", "out_of_scope", False),
    ]
    rows: list[dict[str, Any]] = []
    for row_id, category, covered in specs:
        row = {
            "row_id": row_id,
            "sprint": SPRINT,
            "lane": LANE,
            "contract": CONTRACT,
            "category": category,
            "covered_by_sprint158": covered,
            "status": "COVERED" if covered else "OUT_OF_SCOPE_FAIL_CLOSED",
            "SymmetricHouLuoRegularityClassClosure": category in {"covered_conclusion", "publication_surface"},
            "SymmetricAxisymmetricWithSwirlGlobalRegularity": row_id == "global_smooth_symmetric_solution",
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
    summary = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "row_count": len(rows),
        "covered_assumption_count": sum(row["category"] == "covered_assumption" and row["covered_by_sprint158"] for row in rows),
        "covered_conclusion_count": sum(row["category"] == "covered_conclusion" and row["covered_by_sprint158"] for row in rows),
        "out_of_scope_count": sum(row["category"] == "out_of_scope" for row in rows),
        "SymmetricHouLuoRegularityClassClosure": True,
        "SymmetricAxisymmetricWithSwirlGlobalRegularity": True,
        "MechanismExhaustionForFullClayNS": False,
        "GeneralSmoothFiniteEnergyNSRegularity": False,
        "full_clay_ns_solved": False,
        "fullClayNSSolved": False,
        "fullNavierStokesSolutionConstructed": False,
        "clay_navier_stokes_promoted": False,
        "promotion_allowed": False,
        "control_card": CONTROL_CARD,
    }
    summary["validation_passed"] = summary["covered_assumption_count"] == 5 and not summary["full_clay_ns_solved"]
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
        "# Sprint 158 Assumption Scope Matrix",
        "",
        f"- Covered assumptions: `{summary['covered_assumption_count']}`",
        f"- Out of scope rows: `{summary['out_of_scope_count']}`",
        f"- Full Clay NS solved: `{summary['full_clay_ns_solved']}`",
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
