#!/usr/bin/env python3
"""Sprint 164 topological stretching leakage target emitter.

This script records the next fail-closed Navier-Stokes theorem target after
the Sprint 163 symbol-level alignment obstruction.  It deliberately records a
target surface only: no topological stretching leakage theorem, Sigma
concentration exclusion, critical-alignment exhaustion, or full Clay
Navier-Stokes result is asserted.
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
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint164_topological_stretching_leakage_target"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SUMMARY_NAME = f"{CONTRACT}_summary.json"
ROWS_JSON_NAME = f"{CONTRACT}_rows.json"
ROWS_CSV_NAME = f"{CONTRACT}_rows.csv"
MARKDOWN_NAME = f"{CONTRACT}.md"
MANIFEST_NAME = f"{CONTRACT}_manifest.json"
SPRINT = 164
LANE = 3
DEFAULT_GENERATED_AT = "1970-01-01T00:00:00Z"

TRUE_TARGET_FLAGS = (
    "TopologicalStretchingLeakageTargetRecorded",
    "DegeneracyRidingCascadeTargetRecorded",
)

FALSE_FLAGS = (
    "TopologicalStretchingLeakageLemma",
    "SigmaConcentrationImpossible",
    "CriticalAlignmentTopologicalExhaustion",
    "MechanismExhaustionForFullClayNS",
    "full_clay_ns_solved",
)

VARIABLE_ROWS = (
    {
        "row_id": "V01",
        "variable": "theta0",
        "mathematical_role": "transverse angular-strain degeneracy point",
        "surface": "theta0 in Sigma with M(theta0)=0",
        "target_use": "center the local leakage normal form at the degeneracy.",
    },
    {
        "row_id": "V02",
        "variable": "Sigma",
        "mathematical_role": "degeneracy set of the angular strain symbol",
        "surface": "Sigma subset S^2",
        "target_use": "localize degeneracy-riding cascades in angular frequency.",
    },
    {
        "row_id": "V03",
        "variable": "M(theta)",
        "mathematical_role": "degree-zero angular strain multiplier",
        "surface": "M : S^2 -> Sym_0(3)",
        "target_use": "supply the maximal stretching eigenbundle whose branch structure leaks.",
    },
    {
        "row_id": "V04",
        "variable": "DM(theta0)",
        "mathematical_role": "transversality derivative at the degeneracy",
        "surface": "DM(theta0) tangential directions nonzero",
        "target_use": "compute the local branch-splitting and c_Sigma constants.",
    },
    {
        "row_id": "V05",
        "variable": "c_Sigma",
        "mathematical_role": "putative leakage constant from transverse monodromy",
        "surface": "c_Sigma > 0 target, not proved",
        "target_use": "measure fixed averaged-stretching loss near Sigma if leakage closes.",
    },
    {
        "row_id": "V06",
        "variable": "Pi_plus",
        "mathematical_role": "local maximal-eigenbranch projector",
        "surface": "Pi_plus(theta) near a chosen orientable patch",
        "target_use": "separate branch-following packets from leaked angular mass.",
    },
    {
        "row_id": "V07",
        "variable": "angular variation",
        "mathematical_role": "variation cost of vorticity-frequency defect measure",
        "surface": "AngVar_Sigma(mu_r)",
        "target_use": "quantify the incoherence penalty forced by branch rotation.",
    },
    {
        "row_id": "V08",
        "variable": "branch splitting",
        "mathematical_role": "two-branch alternative near transverse crossing",
        "surface": "maximal eigenvalue branches exchange around theta0",
        "target_use": "record the leakage branch when a packet cannot remain on one eigenbranch.",
    },
    {
        "row_id": "V09",
        "variable": "wedge collapse",
        "mathematical_role": "escape hatch into a thin simply connected wedge at Sigma",
        "surface": "single-branch collapse with shrinking angular support",
        "target_use": "record the unresolved case requiring pressure/coherence control.",
    },
)

CONTROL_CARD = {
    "O": "Sprint164 coding lane 3 owns one normalized topological stretching leakage target script.",
    "R": "Emit JSON, CSV, Markdown, and manifest surfaces for the leakage target while keeping all proof and Clay flags false.",
    "C": "Python stdlib script plus outputs/ns_sprint164_topological_stretching_leakage_target artifacts.",
    "S": "Sprint163 imported a symbol-level obstruction only; this lane records the next microlocal leakage target.",
    "L": "theta0/Sigma/M/DM -> branch splitting or wedge collapse -> c_Sigma leakage target -> no theorem promotion.",
    "P": "Record variables and route alternatives as a fail-closed target ledger.",
    "G": "Pass only if required target flags are true and every theorem/Clay flag is false.",
    "F": "TopologicalStretchingLeakageLemma and SigmaConcentrationImpossible remain open.",
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", "--output-dir", dest="out_dir", type=Path, default=OUT_DIR_DEFAULT)
    parser.add_argument("--generated-at", default=DEFAULT_GENERATED_AT)
    return parser.parse_args()


def stable_hash(value: Any) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def named_flags(names: tuple[str, ...], value: bool) -> dict[str, bool]:
    return {name: value for name in names}


def named_flags_have_value(record: dict[str, Any], names: tuple[str, ...], value: bool) -> bool:
    return all(record.get(name) is value for name in names)


def rows_named_flags_have_value(rows: list[dict[str, Any]], names: tuple[str, ...], value: bool) -> bool:
    return all(named_flags_have_value(row, names, value) for row in rows)


def build_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for index, spec in enumerate(VARIABLE_ROWS, start=1):
        row: dict[str, Any] = {
            "sprint": SPRINT,
            "lane": LANE,
            "contract": CONTRACT,
            "surface_name": "TopologicalStretchingLeakageTarget",
            "target_index": index,
            "status": "TARGET_RECORDED_NOT_PROVED",
            "closed": False,
            "fail_closed": True,
            "target_statement": (
                "Near a transverse Sigma degeneracy, maximal-eigenbranch "
                "monodromy should force branch splitting, wedge collapse, or a "
                "positive c_Sigma stretching leakage cost."
            ),
            **spec,
            **named_flags(TRUE_TARGET_FLAGS, True),
            **named_flags(FALSE_FLAGS, False),
        }
        row["row_hash"] = stable_hash({key: value for key, value in row.items() if key != "row_hash"})
        rows.append(row)
    return rows


def build_summary(repo_root: Path, out_dir: Path, generated_at: str) -> dict[str, Any]:
    rows = build_rows()
    variables = [row["variable"] for row in rows]
    required_variables_present = variables == [row["variable"] for row in VARIABLE_ROWS]

    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "generated_at": generated_at,
        "repo_root": str(repo_root),
        "out_dir": str(out_dir),
        "summary_path": str(out_dir / SUMMARY_NAME),
        "surface_name": "TopologicalStretchingLeakageTarget",
        "decision": "topological_stretching_leakage_target_recorded_fail_closed",
        "scope": "target ledger only",
        "variables": variables,
        "required_variables_present": required_variables_present,
        "row_count": len(rows),
        "rows": rows,
        "target_route": [
            "degeneracy_riding_cascade",
            "branch_splitting",
            "wedge_collapse",
            "c_Sigma_leakage_cost",
        ],
        "control_card": CONTROL_CARD,
        **named_flags(TRUE_TARGET_FLAGS, True),
        **named_flags(FALSE_FLAGS, False),
    }
    summary["row_target_flags_true"] = rows_named_flags_have_value(rows, TRUE_TARGET_FLAGS, True)
    summary["row_false_flags_false"] = rows_named_flags_have_value(rows, FALSE_FLAGS, False)
    summary["summary_target_flags_true"] = named_flags_have_value(summary, TRUE_TARGET_FLAGS, True)
    summary["summary_false_flags_false"] = named_flags_have_value(summary, FALSE_FLAGS, False)
    summary["validation_passed"] = (
        required_variables_present
        and summary["TopologicalStretchingLeakageTargetRecorded"] is True
        and summary["DegeneracyRidingCascadeTargetRecorded"] is True
        and summary["TopologicalStretchingLeakageLemma"] is False
        and summary["SigmaConcentrationImpossible"] is False
        and summary["CriticalAlignmentTopologicalExhaustion"] is False
        and summary["MechanismExhaustionForFullClayNS"] is False
        and summary["full_clay_ns_solved"] is False
        and summary["row_target_flags_true"]
        and summary["row_false_flags_false"]
        and summary["summary_target_flags_true"]
        and summary["summary_false_flags_false"]
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
        "# Sprint 164 Topological Stretching Leakage Target",
        "",
        f"- Surface: `{summary['surface_name']}`",
        f"- Decision: `{summary['decision']}`",
        f"- Target recorded: `{summary['TopologicalStretchingLeakageTargetRecorded']}`",
        f"- Degeneracy-riding cascade target recorded: `{summary['DegeneracyRidingCascadeTargetRecorded']}`",
        f"- Leakage theorem proved: `{summary['TopologicalStretchingLeakageLemma']}`",
        f"- Sigma concentration impossible: `{summary['SigmaConcentrationImpossible']}`",
        f"- Critical alignment exhaustion: `{summary['CriticalAlignmentTopologicalExhaustion']}`",
        f"- Full Clay mechanism exhaustion: `{summary['MechanismExhaustionForFullClayNS']}`",
        f"- Full Clay NS solved: `{summary['full_clay_ns_solved']}`",
        "",
        "## Variables",
        "",
        "| variable | role | surface | target use |",
        "|---|---|---|---|",
    ]
    for row in summary["rows"]:
        lines.append(
            f"| `{row['variable']}` | {row['mathematical_role']} | "
            f"`{row['surface']}` | {row['target_use']} |"
        )
    lines.extend(
        [
            "",
            "## Route",
            "",
            "- Degeneracy-riding cascade: record that the possible cascade is localized near Sigma.",
            "- Branch splitting: record the leakage alternative produced by branch exchange.",
            "- Wedge collapse: record the unresolved escape hatch into thin angular support.",
            "- `c_Sigma`: record the positive leakage constant as a target, not a proof.",
            "",
            "## Control Card",
            "",
        ]
    )
    for key in ("O", "R", "C", "S", "L", "P", "G", "F"):
        lines.append(f"- `{key}`: {summary['control_card'][key]}")
    lines.append("")
    return "\n".join(lines)


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build_manifest(out_dir: Path, generated_at: str, summary: dict[str, Any]) -> dict[str, Any]:
    names = (SUMMARY_NAME, ROWS_JSON_NAME, ROWS_CSV_NAME, MARKDOWN_NAME)
    files = []
    for name in names:
        path = out_dir / name
        files.append(
            {
                "name": name,
                "path": str(path),
                "sha256": file_sha256(path),
                "bytes": path.stat().st_size,
            }
        )
    manifest = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "generated_at": generated_at,
        "artifact_count": len(files),
        "files": files,
        "summary_hash": summary["summary_hash"],
        "validation_passed": summary["validation_passed"],
    }
    manifest["manifest_hash"] = stable_hash(manifest)
    return manifest


def atomic_replace_dir(src: Path, dst: Path) -> None:
    if dst.exists():
        shutil.rmtree(dst)
    src.replace(dst)


def emit(repo_root: Path, out_dir_arg: Path, generated_at: str) -> dict[str, Any]:
    repo_root = repo_root.resolve()
    out_dir = out_dir_arg if out_dir_arg.is_absolute() else repo_root / out_dir_arg
    out_dir = out_dir.resolve()
    out_dir.parent.mkdir(parents=True, exist_ok=True)

    with tempfile.TemporaryDirectory(prefix=f".{CONTRACT}.", dir=str(out_dir.parent)) as tmp_name:
        tmp_dir = Path(tmp_name)
        summary = build_summary(repo_root, out_dir, generated_at)
        rows = summary["rows"]
        write_json(tmp_dir / SUMMARY_NAME, summary)
        write_json(tmp_dir / ROWS_JSON_NAME, rows)
        write_csv(tmp_dir / ROWS_CSV_NAME, rows)
        (tmp_dir / MARKDOWN_NAME).write_text(render_markdown(summary), encoding="utf-8")
        manifest = build_manifest(tmp_dir, generated_at, summary)
        write_json(tmp_dir / MANIFEST_NAME, manifest)
        atomic_replace_dir(tmp_dir, out_dir)

    return {
        "summary": summary,
        "out_dir": str(out_dir),
        "summary_path": str(out_dir / SUMMARY_NAME),
        "manifest_path": str(out_dir / MANIFEST_NAME),
    }


def main() -> int:
    args = parse_args()
    result = emit(args.repo_root, args.out_dir, args.generated_at)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["summary"]["validation_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
