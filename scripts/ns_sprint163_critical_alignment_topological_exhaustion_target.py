#!/usr/bin/env python3
"""Sprint 163 critical-alignment topological exhaustion target emitter."""

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


CONTRACT = "ns_sprint163_critical_alignment_topological_exhaustion_target"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SUMMARY_NAME = f"{CONTRACT}_summary.json"
ROWS_JSON_NAME = f"{CONTRACT}_rows.json"
ROWS_CSV_NAME = f"{CONTRACT}_rows.csv"
MARKDOWN_NAME = f"{CONTRACT}.md"
MANIFEST_NAME = f"{CONTRACT}_manifest.json"
SPRINT = 163
LANE = 3
DEFAULT_GENERATED_AT = "1970-01-01T00:00:00Z"

THEOREM_TARGET = "CriticalAlignmentTopologicalExhaustion"
TARGET_STATEMENT = (
    "If limsup A_r/D_r > 0 in an ancient blowup profile, then vorticity must "
    "concentrate at transverse degeneracy theta0 in Sigma."
)

FALSE_FLAGS = (
    "CriticalAlignmentTopologicalExhaustion",
    "CriticalAlignmentTopologicalExhaustion_proved",
    "BlowupImpliesSigmaConcentration",
    "SigmaConcentrationImpossible",
    "MechanismExhaustionForFullClayNS",
    "full_clay_ns_solved",
    "fullClayNSSolved",
    "fullNavierStokesSolutionConstructed",
    "clay_navier_stokes_promoted",
    "ClayNavierStokesPromoted",
    "promotion_allowed",
)

CONTROL_CARD = {
    "O": "Sprint163 lane 3 owns the critical-alignment topological exhaustion target.",
    "R": "Record the target theorem and its dependency chain without proving concentration or Clay closure.",
    "C": "Python stdlib emitter writes normalized JSON, CSV, Markdown, and manifest artifacts.",
    "S": "Sprint162 left a residual-positive profile fork; Sprint163 records the topological exhaustion target required to advance it.",
    "L": "residual-positive ancient profile -> limsup A_r/D_r > 0 -> Sigma concentration target -> Sanni symbol obstruction -> no Clay promotion.",
    "P": "Use this artifact as a theorem target ledger, not as a proof certificate.",
    "G": "Validation requires the target recorded flag true, all theorem/proof/Clay flags false, and dependency rows including Sprint162 plus Sanni.",
    "F": "Blowup-to-Sigma concentration and Sigma-impossibility are both unproved.",
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


def false_flags() -> dict[str, bool]:
    return {name: False for name in FALSE_FLAGS}


def build_dependency_rows() -> list[dict[str, Any]]:
    specs = [
        {
            "row_id": "D01",
            "dependency_id": "sprint162_route_a_defect_iteration",
            "source_contract": "ns_sprint162_residual_positive_profile_fork",
            "source_sprint": 162,
            "source_lane": 3,
            "chain_role": "regularity_branch_context",
            "statement": "NSCriticalResidual_r <= 0 for every sufficiently small r gives the conditional defect-iteration route.",
            "status": "CONDITIONAL_CONTEXT_NOT_GENERAL_PROOF",
            "supports_target_recording": True,
            "proved": False,
        },
        {
            "row_id": "D02",
            "dependency_id": "sprint162_route_b_residual_positive_profile",
            "source_contract": "ns_sprint162_residual_positive_profile_fork",
            "source_sprint": 162,
            "source_lane": 3,
            "chain_role": "ancient_blowup_profile_trigger",
            "statement": "NSCriticalResidual_r > 0 along r_n -> 0 leaves a residual-positive ancient blowup candidate.",
            "status": "NECESSARY_CONDITION_BOUNDARY",
            "supports_target_recording": True,
            "proved": False,
        },
        {
            "row_id": "D03",
            "dependency_id": "critical_alignment_limsup_ratio",
            "source_contract": CONTRACT,
            "source_sprint": SPRINT,
            "source_lane": LANE,
            "chain_role": "alignment_ratio_hypothesis",
            "statement": "The ancient blowup profile is tested under limsup A_r/D_r > 0.",
            "status": "TARGET_HYPOTHESIS_RECORDED",
            "supports_target_recording": True,
            "proved": False,
        },
        {
            "row_id": "D04",
            "dependency_id": "blowup_implies_sigma_concentration_target",
            "source_contract": CONTRACT,
            "source_sprint": SPRINT,
            "source_lane": LANE,
            "chain_role": "missing_concentration_theorem",
            "statement": "Positive critical alignment ratio should force vorticity concentration at transverse degeneracy theta0 in Sigma.",
            "status": "THEOREM_TARGET_RECORDED_NOT_PROVED",
            "supports_target_recording": True,
            "proved": False,
        },
        {
            "row_id": "D05",
            "dependency_id": "sanni_symbol_obstruction",
            "source_contract": "SanniSymbolObstruction",
            "source_sprint": None,
            "source_lane": None,
            "chain_role": "symbolic_topological_obstruction",
            "statement": "Sanni symbol obstruction blocks replacing the Sigma-degeneracy target by a completed topological impossibility theorem.",
            "status": "OBSTRUCTION_RECORDED",
            "supports_target_recording": True,
            "proved": False,
        },
        {
            "row_id": "D06",
            "dependency_id": "sigma_concentration_impossible_gap",
            "source_contract": CONTRACT,
            "source_sprint": SPRINT,
            "source_lane": LANE,
            "chain_role": "missing_exclusion_theorem",
            "statement": "No theorem proves that vorticity concentration at transverse degeneracy theta0 in Sigma is impossible.",
            "status": "IMPOSSIBILITY_THEOREM_FALSE",
            "supports_target_recording": True,
            "proved": False,
        },
    ]
    rows: list[dict[str, Any]] = []
    for index, spec in enumerate(specs, start=1):
        row: dict[str, Any] = {
            "sprint": SPRINT,
            "lane": LANE,
            "contract": CONTRACT,
            "chain_index": index,
            "theorem_target": THEOREM_TARGET,
            "target_recorded": True,
            **spec,
        }
        row.update(false_flags())
        row["row_hash"] = stable_hash({key: value for key, value in row.items() if key != "row_hash"})
        rows.append(row)
    return rows


def all_false(record: dict[str, Any]) -> bool:
    return all(record.get(name) is False for name in FALSE_FLAGS)


def rows_all_false(rows: list[dict[str, Any]]) -> bool:
    return all(all_false(row) for row in rows)


def build_summary(repo_root: Path, out_dir: Path, generated_at: str) -> dict[str, Any]:
    rows = build_dependency_rows()
    dependency_ids = {row["dependency_id"] for row in rows}
    sprint162_rows_present = {
        "sprint162_route_a_defect_iteration",
        "sprint162_route_b_residual_positive_profile",
    }.issubset(dependency_ids)
    sanni_obstruction_present = "sanni_symbol_obstruction" in dependency_ids
    target_rows_present = {
        "critical_alignment_limsup_ratio",
        "blowup_implies_sigma_concentration_target",
        "sigma_concentration_impossible_gap",
    }.issubset(dependency_ids)

    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "generated_at": generated_at,
        "repo_root": str(repo_root),
        "out_dir": str(out_dir),
        "summary_path": str(out_dir / SUMMARY_NAME),
        "surface_name": "CriticalAlignmentTopologicalExhaustionTarget",
        "decision": "critical_alignment_topological_exhaustion_target_recorded_fail_closed",
        "theorem_target": THEOREM_TARGET,
        "target_statement": TARGET_STATEMENT,
        "target_recorded": True,
        "theorem_proved": False,
        "CriticalAlignmentTopologicalExhaustion_recorded": True,
        "CriticalAlignmentTopologicalExhaustion_proved": False,
        "BlowupImpliesSigmaConcentration": False,
        "SigmaConcentrationImpossible": False,
        "full_clay_ns_solved": False,
        "dependency_chain_rows": rows,
        "dependency_chain_row_count": len(rows),
        "dependency_chain_ids": [row["dependency_id"] for row in rows],
        "sprint162_residual_fork_dependencies_present": sprint162_rows_present,
        "sanni_symbol_obstruction_present": sanni_obstruction_present,
        "target_rows_present": target_rows_present,
        "ancient_blowup_profile_condition": "limsup A_r/D_r > 0",
        "forced_concentration_locus": "transverse degeneracy theta0 in Sigma",
        "row_false_flags_false": rows_all_false(rows),
        "control_card": CONTROL_CARD,
    }
    summary.update({name: summary.get(name, False) for name in FALSE_FLAGS})
    summary["summary_false_flags_false"] = all_false(summary)
    summary["validation_passed"] = (
        summary["target_recorded"]
        and summary["CriticalAlignmentTopologicalExhaustion_recorded"]
        and summary["theorem_proved"] is False
        and summary["CriticalAlignmentTopologicalExhaustion_proved"] is False
        and summary["BlowupImpliesSigmaConcentration"] is False
        and summary["SigmaConcentrationImpossible"] is False
        and summary["full_clay_ns_solved"] is False
        and sprint162_rows_present
        and sanni_obstruction_present
        and target_rows_present
        and summary["row_false_flags_false"]
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
        "# Sprint 163 Critical Alignment Topological Exhaustion Target",
        "",
        f"- Surface: `{summary['surface_name']}`",
        f"- Decision: `{summary['decision']}`",
        f"- Theorem target: `{summary['theorem_target']}`",
        f"- Target recorded: `{summary['target_recorded']}`",
        f"- Theorem proved: `{summary['theorem_proved']}`",
        f"- BlowupImpliesSigmaConcentration: `{summary['BlowupImpliesSigmaConcentration']}`",
        f"- SigmaConcentrationImpossible: `{summary['SigmaConcentrationImpossible']}`",
        f"- Full Clay NS solved: `{summary['full_clay_ns_solved']}`",
        f"- Validation passed: `{summary['validation_passed']}`",
        "",
        summary["target_statement"],
        "",
        "| index | dependency | role | status | proved |",
        "| ---: | --- | --- | --- | ---: |",
    ]
    for row in summary["dependency_chain_rows"]:
        lines.append(
            f"| {row['chain_index']} | {row['dependency_id']} | "
            f"{row['chain_role']} | {row['status']} | {row['proved']} |"
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
    summary = build_summary(repo_root, out_dir, args.generated_at)

    out_dir.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=f".{CONTRACT}.", dir=out_dir.parent) as temp_name:
        temp_dir = Path(temp_name)
        write_json(temp_dir / ROWS_JSON_NAME, summary["dependency_chain_rows"])
        write_csv(temp_dir / ROWS_CSV_NAME, summary["dependency_chain_rows"])
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
