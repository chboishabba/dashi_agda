#!/usr/bin/env python3
"""Sprint 159 mechanism exhaustion gap emitter."""

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


CONTRACT = "ns_sprint159_mechanism_exhaustion_gap"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SPRINT = 159
LANE = 3

OPEN_EXTERNAL_AUTHORITY_BOUNDARY = "OPEN_EXTERNAL_AUTHORITY_BOUNDARY"
OPEN_STRUCTURAL_GAP = "OPEN_STRUCTURAL_GAP"

CLAY_FLAGS = (
    "MechanismExhaustionForFullClayNS",
    "GeneralSmoothFiniteEnergyNSRegularity",
    "full_clay_ns_solved",
    "fullClayNSSolved",
    "fullNavierStokesSolutionConstructed",
    "clay_navier_stokes_promoted",
    "promotion_allowed",
    "ClaySubmissionReady",
    "ClaySubmissionPromotionPacket",
)

EXPECTED_BLOCKERS = (
    "GeneralDataReductionToCriticalProfiles",
    "CriticalProfileCompactnessForNS",
    "AxisymmetricOrSymmetricReductionExclusion",
    "NonAxisymmetricVortexStretchingControl",
    "PressureNonlocalityClosureForGeneralData",
    "CriticalNormExhaustionCriterion",
    "FullNavierStokesContinuationBridge",
    "ClaySubmissionPromotionPacket",
)

CONTROL_CARD = {
    "O": "Worker 3 owns the Sprint159 mechanism-exhaustion gap emitter.",
    "R": "List the exact open lemmas blocking full general-data Navier-Stokes and Clay promotion.",
    "C": "Python stdlib emitter writes blocker rows to JSON, CSV, Markdown, and manifest.",
    "S": "Sprint157/158 close the symmetric Hou-Luo packet only; general-data mechanism exhaustion remains open.",
    "L": "critical profiles -> compactness -> exclusion/control/pressure closure -> continuation bridge -> Clay packet.",
    "P": "Use this as a fail-closed gap ledger for Sprint159 lane 3.",
    "G": "Validation requires every blocker row to be present and every Clay flag to remain false.",
    "F": "External Clay submission authority and structural general-data lemmas are still absent.",
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
        (
            "GeneralDataReductionToCriticalProfiles",
            OPEN_STRUCTURAL_GAP,
            "No reduction from arbitrary smooth finite-energy 3D data to a closed critical-profile family.",
            ["outputs/ns_sprint158_assumption_scope_matrix/ns_sprint158_assumption_scope_matrix_summary.json"],
        ),
        (
            "CriticalProfileCompactnessForNS",
            OPEN_STRUCTURAL_GAP,
            "No compactness theorem for the required general Navier-Stokes critical profiles.",
            ["outputs/ns_sprint158_assumption_scope_matrix/ns_sprint158_assumption_scope_matrix_summary.json"],
        ),
        (
            "AxisymmetricOrSymmetricReductionExclusion",
            OPEN_STRUCTURAL_GAP,
            "The symmetric Hou-Luo closure does not exclude all nonsymmetric or nonaxisymmetric blowup routes.",
            [
                "outputs/ns_sprint157_symmetric_hou_luo_regular_class/ns_sprint157_symmetric_hou_luo_regular_class_summary.json",
                "outputs/ns_sprint158_theorem_statement_closure/ns_sprint158_theorem_statement_closure_summary.json",
            ],
        ),
        (
            "NonAxisymmetricVortexStretchingControl",
            OPEN_STRUCTURAL_GAP,
            "No general nonaxisymmetric vortex-stretching control replaces the symmetric route estimates.",
            ["outputs/ns_sprint158_theorem_statement_closure/ns_sprint158_theorem_statement_closure_summary.json"],
        ),
        (
            "PressureNonlocalityClosureForGeneralData",
            OPEN_STRUCTURAL_GAP,
            "No full pressure-nonlocality closure is available for arbitrary 3D data.",
            ["outputs/ns_sprint158_assumption_scope_matrix/ns_sprint158_assumption_scope_matrix_summary.json"],
        ),
        (
            "CriticalNormExhaustionCriterion",
            OPEN_STRUCTURAL_GAP,
            "No criterion proves every critical norm concentration scenario is exhausted.",
            ["outputs/ns_sprint157_bkm_integral_estimate/ns_sprint157_bkm_integral_estimate_summary.json"],
        ),
        (
            "FullNavierStokesContinuationBridge",
            OPEN_STRUCTURAL_GAP,
            "Sprint157 continuation is scoped to the symmetric class, not full general-data Navier-Stokes.",
            [
                "outputs/ns_sprint157_continuation_bridge/ns_sprint157_continuation_bridge_summary.json",
                "outputs/ns_sprint158_theorem_statement_closure/ns_sprint158_theorem_statement_closure_summary.json",
            ],
        ),
        (
            "ClaySubmissionPromotionPacket",
            OPEN_EXTERNAL_AUTHORITY_BOUNDARY,
            "No Clay submission packet can be promoted without structural closure and external authority review.",
            ["outputs/ns_sprint158_publication_packet_readiness/ns_sprint158_publication_packet_readiness_summary.json"],
        ),
    ]
    rows: list[dict[str, Any]] = []
    for lemma, status, blocker, support_links in specs:
        row: dict[str, Any] = {
            "row_id": lemma,
            "lemma": lemma,
            "sprint": SPRINT,
            "lane": LANE,
            "contract": CONTRACT,
            "status": status,
            "blocker_present": True,
            "blocker": blocker,
            "support_links": support_links,
            "supported_by_sprint157": any("sprint157" in link for link in support_links),
            "supported_by_sprint158": any("sprint158" in link for link in support_links),
            "open_external_authority_boundary": status == OPEN_EXTERNAL_AUTHORITY_BOUNDARY,
            "open_structural_gap": status == OPEN_STRUCTURAL_GAP,
        }
        row.update(clay_flag_fields())
        row["row_hash"] = stable_hash({k: v for k, v in row.items() if k != "row_hash"})
        rows.append(row)
    return rows


def clay_flags_false(records: list[dict[str, Any]] | list[dict[str, bool]] | dict[str, Any]) -> bool:
    if isinstance(records, dict):
        return all(records.get(flag) is False for flag in CLAY_FLAGS)
    return all(all(record.get(flag) is False for flag in CLAY_FLAGS) for record in records)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    present_blockers = tuple(row["lemma"] for row in rows if row["blocker_present"])
    expected_blockers_present = set(present_blockers) == set(EXPECTED_BLOCKERS) and len(rows) == len(EXPECTED_BLOCKERS)
    open_statuses_valid = all(row["status"] in {OPEN_EXTERNAL_AUTHORITY_BOUNDARY, OPEN_STRUCTURAL_GAP} for row in rows)
    row_clay_flags_false = clay_flags_false(rows)
    summary = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "row_count": len(rows),
        "decision": "mechanism_exhaustion_gap_fail_closed",
        "expected_blockers": list(EXPECTED_BLOCKERS),
        "present_blockers": list(present_blockers),
        "expected_blockers_present": expected_blockers_present,
        "open_statuses_valid": open_statuses_valid,
        "all_listed_blockers_present": expected_blockers_present and all(row["blocker_present"] for row in rows),
        "row_clay_flags_false": row_clay_flags_false,
        "open_structural_gap_count": sum(row["status"] == OPEN_STRUCTURAL_GAP for row in rows),
        "open_external_authority_boundary_count": sum(row["status"] == OPEN_EXTERNAL_AUTHORITY_BOUNDARY for row in rows),
        "support_links_include_sprint157": any(row["supported_by_sprint157"] for row in rows),
        "support_links_include_sprint158": any(row["supported_by_sprint158"] for row in rows),
        "control_card": CONTROL_CARD,
    }
    summary.update(clay_flag_fields())
    summary["summary_clay_flags_false"] = clay_flags_false(summary)
    summary["validation_passed"] = (
        summary["all_listed_blockers_present"]
        and summary["open_statuses_valid"]
        and summary["row_clay_flags_false"]
        and summary["summary_clay_flags_false"]
    )
    summary["summary_hash"] = stable_hash({k: v for k, v in summary.items() if k != "summary_hash"})
    return summary


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = list(rows[0].keys())
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def render_markdown(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# Sprint 159 Mechanism Exhaustion Gap",
        "",
        f"- Decision: `{summary['decision']}`",
        f"- Validation passed: `{summary['validation_passed']}`",
        f"- Full Clay NS solved: `{summary['full_clay_ns_solved']}`",
        f"- Clay submission promoted: `{summary['clay_navier_stokes_promoted']}`",
        "",
        "| lemma | status | blocker_present | support_links |",
        "| --- | --- | ---: | --- |",
    ]
    for row in rows:
        links = "<br>".join(row["support_links"])
        lines.append(f"| {row['lemma']} | {row['status']} | {row['blocker_present']} | {links} |")
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
