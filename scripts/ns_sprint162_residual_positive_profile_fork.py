#!/usr/bin/env python3
"""Sprint 162 residual-positive profile theorem-fork emitter."""

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


CONTRACT = "ns_sprint162_residual_positive_profile_fork"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SUMMARY_NAME = f"{CONTRACT}_summary.json"
ROWS_JSON_NAME = f"{CONTRACT}_rows.json"
ROWS_CSV_NAME = f"{CONTRACT}_rows.csv"
MARKDOWN_NAME = f"{CONTRACT}.md"
MANIFEST_NAME = f"{CONTRACT}_manifest.json"
SPRINT = 162
LANE = 3
DEFAULT_GENERATED_AT = "1970-01-01T00:00:00Z"

FALSE_FLAGS = (
    "NoPersistentPositiveNSCriticalResidual",
    "PressureStretchingDepletionLemma",
    "MechanismExhaustionForFullClayNS",
    "full_clay_ns_solved",
    "fullClayNSSolved",
    "fullNavierStokesSolutionConstructed",
    "clayNavierStokesPromoted",
    "promotion_allowed",
)

OBSERVABLES = (
    "local_defect_D_r",
    "pressure_flux_integral",
    "stretching_alignment_A_r",
    "localized_dissipation",
    "critical_residual_sign",
    "residual_positive_sequence_frequency",
)

CONTROL_CARD = {
    "O": "Sprint162 lane 3 owns the residual-positive profile fork ledger.",
    "R": "Separate the regularity fork from the residual-positive blowup-candidate fork.",
    "C": "One JSON summary records route A, route B, numerical observables, and fail-closed promotion flags.",
    "S": "The repo has a scoped symmetric regularity result, not a general residual depletion theorem.",
    "L": "residual <= 0 -> defect iteration/CKN; residual > 0 sequence -> necessary blowup-profile condition.",
    "P": "Use the fork as a falsifiable target without claiming Clay closure.",
    "G": "Validation requires both routes present and all Clay flags false.",
    "F": "The gap is proving route A for all possible small scales and all general 3D data.",
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


def build_fork_rows() -> list[dict[str, Any]]:
    rows = [
        {
            "route_id": "A",
            "route_name": "defect_iteration_regularity_route",
            "condition": "NSCriticalResidual_r <= 0 for every sufficiently small r",
            "consequence": "D_r decays by iteration, reaches the CKN epsilon threshold, and rules out the singular point",
            "status": "CONDITIONAL_NOT_PROVED_FOR_GENERAL_DATA",
            "clay_closing_if_universal": True,
            "proved_universal": False,
        },
        {
            "route_id": "B",
            "route_name": "residual_positive_blowup_candidate_route",
            "condition": "NSCriticalResidual_r > 0 along a sequence r_n -> 0",
            "consequence": "Any finite-time blowup profile must carry persistent non-axisymmetric pressure/strain/vorticity residual",
            "status": "NECESSARY_CONDITION_BOUNDARY",
            "clay_closing_if_universal": False,
            "proved_universal": False,
        },
    ]
    for row in rows:
        row.update({"sprint": SPRINT, "lane": LANE, "contract": CONTRACT})
        row.update(false_flags())
        row["row_hash"] = stable_hash({k: v for k, v in row.items() if k != "row_hash"})
    return rows


def build_summary(repo_root: Path, out_dir: Path, generated_at: str) -> dict[str, Any]:
    rows = build_fork_rows()
    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "generated_at": generated_at,
        "repo_root": str(repo_root),
        "out_dir": str(out_dir),
        "summary_path": str(out_dir / SUMMARY_NAME),
        "surface_name": "ResidualPositiveProfileFork",
        "decision": "residual_positive_profile_fork_fail_closed",
        "fork_rows": rows,
        "route_a_present": any(row["route_id"] == "A" for row in rows),
        "route_b_present": any(row["route_id"] == "B" for row in rows),
        "theorem_target": "BlowupImpliesPersistentPositiveNSCriticalResidual",
        "clay_closing_missing_theorem": "NoPersistentPositiveNSCriticalResidual",
        "measured_or_numerical_observables": list(OBSERVABLES),
        "observable_count": len(OBSERVABLES),
        "control_card": CONTROL_CARD,
    }
    summary.update(false_flags())
    summary["all_fail_closed_flags_false"] = all(summary[name] is False for name in FALSE_FLAGS)
    summary["row_fail_closed_flags_false"] = all(
        all(row[name] is False for name in FALSE_FLAGS) for row in rows
    )
    summary["validation_passed"] = (
        summary["route_a_present"]
        and summary["route_b_present"]
        and summary["observable_count"] == 6
        and summary["all_fail_closed_flags_false"]
        and summary["row_fail_closed_flags_false"]
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


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# Sprint 162 Residual Positive Profile Fork",
        "",
        f"- Surface: `{summary['surface_name']}`",
        f"- Decision: `{summary['decision']}`",
        f"- Theorem target: `{summary['theorem_target']}`",
        f"- Clay-closing missing theorem: `{summary['clay_closing_missing_theorem']}`",
        f"- Validation passed: `{summary['validation_passed']}`",
        "",
        "| route | condition | consequence | status |",
        "| --- | --- | --- | --- |",
    ]
    for row in summary["fork_rows"]:
        lines.append(f"| {row['route_id']} | {row['condition']} | {row['consequence']} | {row['status']} |")
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
        write_json(temp_dir / ROWS_JSON_NAME, summary["fork_rows"])
        write_csv(temp_dir / ROWS_CSV_NAME, summary["fork_rows"])
        write_json(temp_dir / SUMMARY_NAME, summary)
        (temp_dir / MARKDOWN_NAME).write_text(render_markdown(summary), encoding="utf-8")
        write_json(temp_dir / MANIFEST_NAME, build_manifest(temp_dir, summary))
        if out_dir.exists():
            shutil.rmtree(out_dir)
        os.replace(temp_dir, out_dir)
        write_json(out_dir / MANIFEST_NAME, build_manifest(out_dir, summary))

    print(json.dumps({"contract": CONTRACT, "summary": str(out_dir / SUMMARY_NAME), "validation_passed": summary["validation_passed"]}, sort_keys=True))
    return 0 if summary["validation_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
