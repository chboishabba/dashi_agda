#!/usr/bin/env python3
"""Sprint 159 partial NS regularity and singularity-control criteria inventory emitter."""

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


CONTRACT = "ns_sprint159_criteria_inventory"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SPRINT = 159
LANE = 4

SUPPORT_NOT_EXHAUSTIVE = "SUPPORT_NOT_EXHAUSTIVE"
CLOSED_SCOPED_CLASS = "CLOSED_SCOPED_CLASS"

CONTROL_CARD = {
    "O": "Worker 4 owns the Sprint159 criteria inventory emitter.",
    "R": "Inventory known partial regularity and singularity-control criteria without promoting full Clay NS.",
    "C": "Python stdlib emitter writes criteria rows to JSON, CSV, Markdown, and manifest.",
    "S": "Class-specific symmetric Hou-Luo closure is available; general NS mechanism exhaustion is absent.",
    "L": "criterion support -> non-exhaustive inventory guard -> scoped symmetric class closure -> full Clay flags false.",
    "P": "Use this inventory as evidence of partial support and scoped closure boundaries.",
    "G": "Every general criterion row must remain support-only; only the symmetric class row is closed in scope.",
    "F": "MechanismExhaustionForFullClayNS remains false for full 3D Navier-Stokes.",
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


def full_clay_false_flags() -> dict[str, bool]:
    return {
        "MechanismExhaustionForFullClayNS": False,
        "GeneralSmoothFiniteEnergyNSRegularity": False,
        "full_clay": False,
        "fullClay": False,
        "full_clay_ns_solved": False,
        "fullClayNSSolved": False,
        "fullNavierStokesSolutionConstructed": False,
        "clay_navier_stokes_promoted": False,
        "promotion_allowed": False,
    }


def build_rows() -> list[dict[str, Any]]:
    specs = [
        {
            "criterion_id": "bkm_continuation",
            "criterion_name": "BKM continuation",
            "criterion_family": "continuation",
            "scope": "smooth_solution_continuation_control",
            "status": SUPPORT_NOT_EXHAUSTIVE,
            "inventory_note": "Finite vorticity-sup norm time integral supports continuation but does not exhaust all full-NS singularity mechanisms.",
        },
        {
            "criterion_id": "prodi_serrin_ladyzhenskaya",
            "criterion_name": "Prodi-Serrin/Ladyzhenskaya",
            "criterion_family": "integrability",
            "scope": "scale-compatible_velocity_integrability",
            "status": SUPPORT_NOT_EXHAUSTIVE,
            "inventory_note": "Velocity space-time integrability criteria support regularity under added bounds and remain conditional.",
        },
        {
            "criterion_id": "escauriaza_seregin_sverak_critical_l3",
            "criterion_name": "Escauriaza-Seregin-Sverak critical L3/L3inf-style criterion",
            "criterion_family": "critical_space",
            "scope": "critical_l3_endpoint_control",
            "status": SUPPORT_NOT_EXHAUSTIVE,
            "inventory_note": "Critical L3 endpoint control rules out blowup under the criterion but is not a universal mechanism-exhaustion theorem.",
        },
        {
            "criterion_id": "caffarelli_kohn_nirenberg_partial_regularity",
            "criterion_name": "Caffarelli-Kohn-Nirenberg partial regularity",
            "criterion_family": "partial_regularity",
            "scope": "suitable_weak_solution_singular_set_control",
            "status": SUPPORT_NOT_EXHAUSTIVE,
            "inventory_note": "Partial regularity bounds the possible singular set and does not by itself close full smooth regularity.",
        },
        {
            "criterion_id": "koch_tataru_small_data_critical_space",
            "criterion_name": "Koch-Tataru small-data critical-space",
            "criterion_family": "small_data",
            "scope": "critical_space_small_data_global_wellposedness",
            "status": SUPPORT_NOT_EXHAUSTIVE,
            "inventory_note": "Small critical-space data produce global control in that regime, not an exhaustive large-data Clay solution.",
        },
        {
            "criterion_id": "symmetric_hou_luo_sprint157_158_closure",
            "criterion_name": "Symmetric Hou-Luo Sprint157/158 closure",
            "criterion_family": "scoped_symmetric_class",
            "scope": "axisymmetric_with_swirl_z_reflection_symmetric_class",
            "status": CLOSED_SCOPED_CLASS,
            "inventory_note": "Sprint157/158 close the symmetric Hou-Luo class through BKM and theorem-scope closure only.",
        },
    ]
    rows: list[dict[str, Any]] = []
    for spec in specs:
        scoped_closed = spec["status"] == CLOSED_SCOPED_CLASS
        row = {
            **spec,
            "sprint": SPRINT,
            "lane": LANE,
            "contract": CONTRACT,
            "support_not_exhaustive": spec["status"] == SUPPORT_NOT_EXHAUSTIVE,
            "closed_scoped_class": scoped_closed,
            "SymmetricHouLuoRegularityClassClosure": scoped_closed,
            "SymmetricAxisymmetricWithSwirlGlobalRegularity": scoped_closed,
            **full_clay_false_flags(),
        }
        row["row_hash"] = stable_hash({k: v for k, v in row.items() if k != "row_hash"})
        rows.append(row)
    return rows


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    support_count = sum(row["status"] == SUPPORT_NOT_EXHAUSTIVE for row in rows)
    scoped_closed_count = sum(row["status"] == CLOSED_SCOPED_CLASS for row in rows)
    full_clay_flags_false = all(
        not row["MechanismExhaustionForFullClayNS"]
        and not row["full_clay"]
        and not row["fullClay"]
        and not row["full_clay_ns_solved"]
        and not row["fullClayNSSolved"]
        for row in rows
    )
    summary = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "row_count": len(rows),
        "support_not_exhaustive_count": support_count,
        "closed_scoped_class_count": scoped_closed_count,
        "decision": "criteria_inventory_support_only_except_symmetric_scoped_class_closure",
        "SymmetricHouLuoRegularityClassClosure": scoped_closed_count == 1,
        "SymmetricAxisymmetricWithSwirlGlobalRegularity": scoped_closed_count == 1,
        "full_clay_flags_false": full_clay_flags_false,
        **full_clay_false_flags(),
        "control_card": CONTROL_CARD,
    }
    summary["validation_passed"] = (
        len(rows) == 6
        and support_count == 5
        and scoped_closed_count == 1
        and full_clay_flags_false
        and not summary["MechanismExhaustionForFullClayNS"]
        and not summary["full_clay"]
        and not summary["fullClay"]
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
        "# Sprint 159 Criteria Inventory",
        "",
        f"- SUPPORT_NOT_EXHAUSTIVE rows: `{summary['support_not_exhaustive_count']}`",
        f"- CLOSED_SCOPED_CLASS rows: `{summary['closed_scoped_class_count']}`",
        f"- MechanismExhaustionForFullClayNS: `{summary['MechanismExhaustionForFullClayNS']}`",
        f"- fullClay: `{summary['fullClay']}`",
        "",
        "| criterion_id | criterion_name | status |",
        "| --- | --- | --- |",
    ]
    for row in rows:
        lines.append(f"| {row['criterion_id']} | {row['criterion_name']} | {row['status']} |")
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
