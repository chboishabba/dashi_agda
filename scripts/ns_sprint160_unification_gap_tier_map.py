#!/usr/bin/env python3
"""Sprint 160 unification gap tier map emitter."""

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


CONTRACT = "ns_sprint160_unification_gap_tier_map"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SPRINT = 160
LANE = 4

PROMOTION_FALSE_FLAGS = (
    "full_unification_promoted",
    "fullUnificationPromoted",
    "full_clay_ns_promoted",
    "fullClayNSPromoted",
    "continuum_ym_mass_gap_promoted",
    "continuumYMMassGapPromoted",
    "clay_navier_stokes_promoted",
    "clay_yang_mills_promoted",
    "promotion_allowed",
)

EXPECTED_TIERS = ("Tier0", "Tier1", "Tier2", "Tier3", "Tier4", "TierX")

CONTROL_CARD = {
    "O": "Worker 4 owns the Sprint160 unification gap tier map emitter.",
    "R": "Map finite local closures and external continuum boundaries without promoting full unification, Clay NS, or continuum YM mass gap.",
    "C": "Python stdlib emitter writes tier rows to JSON, CSV, Markdown, and manifest.",
    "S": "Scope closures, empirical promotion, finite receipts, chemistry rules, and Maxwell/Hodge bridge work are separated from external Clay/YM boundaries.",
    "L": "tiered closure map -> priority queue -> promotion guards remain false.",
    "P": "Use this artifact to sequence SM/Higgs observable bridge first and Hodge/Maxwell finite bridge second.",
    "G": "Validation requires every expected tier once, SM/Higgs priority before Hodge/Maxwell, and all promotion flags false.",
    "F": "Full unification, Clay Navier-Stokes, and continuum Yang-Mills mass-gap promotion are external boundaries.",
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


def promotion_false_flags() -> dict[str, bool]:
    return {flag: False for flag in PROMOTION_FALSE_FLAGS}


def build_rows() -> list[dict[str, Any]]:
    specs = [
        {
            "tier": "Tier0",
            "tier_rank": 0,
            "tier_name": "scope_closures_authority_boundary_decisions",
            "status": "CLOSED_SCOPED_AUTHORITY_BOUNDARY",
            "gap_class": "governance_scope",
            "claim_scope": "scope closures and authority-boundary decisions",
            "next_action_priority": 3,
            "next_action": "maintain fail-closed authority guards while downstream bridges are evaluated",
            "local_promotion_allowed": True,
            "external_boundary": False,
        },
        {
            "tier": "Tier1",
            "tier_rank": 1,
            "tier_name": "empirical_observable_promotion",
            "status": "NEXT_PRIORITY",
            "gap_class": "empirical_bridge",
            "claim_scope": "empirical observable promotion",
            "next_action_priority": 1,
            "next_action": "prioritize SM/Higgs observable bridge and receipt-backed comparison law",
            "local_promotion_allowed": True,
            "external_boundary": False,
        },
        {
            "tier": "Tier2",
            "tier_rank": 2,
            "tier_name": "constants_metrology_receipts",
            "status": "RECEIPT_LEDGER_SUPPORT",
            "gap_class": "metrology_receipt",
            "claim_scope": "constants/metrology receipts",
            "next_action_priority": 4,
            "next_action": "keep constants and metrology receipts synchronized with observable bridge inputs",
            "local_promotion_allowed": True,
            "external_boundary": False,
        },
        {
            "tier": "Tier3",
            "tier_rank": 3,
            "tier_name": "chemistry_finite_rules",
            "status": "FINITE_RULE_SUPPORT",
            "gap_class": "finite_rule_system",
            "claim_scope": "chemistry finite rules",
            "next_action_priority": 5,
            "next_action": "retain finite chemistry rules as support-only until observable and geometry bridges stabilize",
            "local_promotion_allowed": True,
            "external_boundary": False,
        },
        {
            "tier": "Tier4",
            "tier_rank": 4,
            "tier_name": "maxwell_hodge_star_finite_geometry_bridge",
            "status": "SECOND_PRIORITY",
            "gap_class": "finite_geometry_bridge",
            "claim_scope": "Maxwell/Hodge* finite geometry bridge",
            "canonical_tier_label": "Tier4 Maxwell/Hodge",
            "next_action_priority": 2,
            "next_action": "advance Hodge/Maxwell finite geometry bridge after SM/Higgs observable bridge",
            "local_promotion_allowed": True,
            "external_boundary": False,
        },
        {
            "tier": "TierX",
            "tier_rank": 99,
            "tier_name": "clay_ns_continuum_ym_mass_gap_external_boundary",
            "status": "EXTERNAL_BOUNDARY_FAIL_CLOSED",
            "gap_class": "external_continuum_boundary",
            "claim_scope": "Clay NS and continuum YM mass-gap external boundary",
            "canonical_tier_label": "TierX Clay",
            "next_action_priority": 99,
            "next_action": "do not promote full unification, Clay NS, or continuum YM mass gap from finite tier artifacts",
            "local_promotion_allowed": False,
            "external_boundary": True,
        },
    ]
    rows: list[dict[str, Any]] = []
    for spec in specs:
        row: dict[str, Any] = {
            **spec,
            "sprint": SPRINT,
            "lane": LANE,
            "contract": CONTRACT,
            "canonical_tier_label": spec.get("canonical_tier_label", spec["tier"]),
            "SMHiggsObservableBridgePriority": spec["tier"] == "Tier1",
            "HodgeMaxwellFiniteGeometryBridgePriority": spec["tier"] == "Tier4",
            "ClayNSExternalBoundary": spec["tier"] == "TierX",
            "ContinuumYMMassGapExternalBoundary": spec["tier"] == "TierX",
            "FullUnificationExternalBoundary": spec["tier"] == "TierX",
        }
        row.update(promotion_false_flags())
        row["row_hash"] = stable_hash({k: v for k, v in row.items() if k != "row_hash"})
        rows.append(row)
    return rows


def promotion_flags_false(records: list[dict[str, Any]] | dict[str, Any]) -> bool:
    if isinstance(records, dict):
        return all(records.get(flag) is False for flag in PROMOTION_FALSE_FLAGS)
    return all(all(record.get(flag) is False for flag in PROMOTION_FALSE_FLAGS) for record in records)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    tiers = tuple(row["tier"] for row in rows)
    expected_tiers_present = tiers == EXPECTED_TIERS
    priority_rows = sorted(rows, key=lambda row: row["next_action_priority"])
    priority_order = [row["tier"] for row in priority_rows]
    priority_valid = priority_order[:2] == ["Tier1", "Tier4"] and priority_order[-1] == "TierX"
    row_promotion_flags_false = promotion_flags_false(rows)
    external_boundary_valid = any(
        row["tier"] == "TierX"
        and row["external_boundary"]
        and not row["local_promotion_allowed"]
        and row["ClayNSExternalBoundary"]
        and row["ContinuumYMMassGapExternalBoundary"]
        and row["FullUnificationExternalBoundary"]
        for row in rows
    )
    summary = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "row_count": len(rows),
        "decision": "unification_gap_tier_map_fail_closed",
        "expected_tiers": list(EXPECTED_TIERS),
        "present_tiers": list(tiers),
        "expected_tiers_present": expected_tiers_present,
        "next_action_priority": [
            {
                "priority": row["next_action_priority"],
                "tier": row["tier"],
                "next_action": row["next_action"],
            }
            for row in priority_rows
        ],
        "next_action_priority_favors": [
            "SM/Higgs observable bridge",
            "Hodge/Maxwell finite geometry bridge",
        ],
        "canonical_tier_terms": [
            "Tier4 Maxwell/Hodge",
            "TierX Clay",
        ],
        "priority_valid": priority_valid,
        "row_promotion_flags_false": row_promotion_flags_false,
        "external_boundary_valid": external_boundary_valid,
        "SMHiggsObservableBridgePriority": priority_order[0] == "Tier1",
        "HodgeMaxwellAfterSMHiggs": priority_order[1] == "Tier4",
        "FullUnificationExternalBoundary": external_boundary_valid,
        "ClayNSExternalBoundary": external_boundary_valid,
        "ContinuumYMMassGapExternalBoundary": external_boundary_valid,
        "control_card": CONTROL_CARD,
    }
    summary.update(promotion_false_flags())
    summary["summary_promotion_flags_false"] = promotion_flags_false(summary)
    summary["validation_passed"] = (
        expected_tiers_present
        and priority_valid
        and row_promotion_flags_false
        and summary["summary_promotion_flags_false"]
        and external_boundary_valid
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
        "# Sprint 160 Unification Gap Tier Map",
        "",
        f"- Decision: `{summary['decision']}`",
        f"- Validation passed: `{summary['validation_passed']}`",
        "- Canonical tier terms: `Tier4 Maxwell/Hodge`, `TierX Clay`",
        f"- Full unification promoted: `{summary['full_unification_promoted']}`",
        f"- Clay NS promoted: `{summary['clay_navier_stokes_promoted']}`",
        f"- Continuum YM mass gap promoted: `{summary['continuum_ym_mass_gap_promoted']}`",
        "",
        "## Next Action Priority",
        "",
    ]
    for item in summary["next_action_priority"]:
        lines.append(f"- {item['priority']}: {item['tier']} - {item['next_action']}")
    lines.extend(
        [
            "",
            "| tier | claim_scope | status | next_action_priority |",
            "| --- | --- | --- | ---: |",
        ]
    )
    for row in rows:
        lines.append(
            f"| {row['tier']} | {row['claim_scope']} | {row['status']} | {row['next_action_priority']} |"
        )
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
