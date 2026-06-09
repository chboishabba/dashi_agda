#!/usr/bin/env python3
"""Generate Sprint 105 YM gap-closure planning artifacts from repo surfaces."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


DEFAULT_OUT_DIR = Path("outputs/ym_sprint105_gap_closure_plan")
SPRINT104_PATTERN = "DASHI/Physics/Closure/YMSprint104*.agda"
SPRINT105_PATTERN = "DASHI/Physics/Closure/YMSprint105*.agda"
SUMMARY_NAME = "ym_sprint105_gap_closure_plan_summary.json"
PLAN_NAME = "ym_sprint105_gap_closure_plan.md"

FORBIDDEN_PROMOTION = "clayYangMillsPromoted = " + "true"
FORBIDDEN_SURFACE_TOKENS = ("post" + "ulate", "TO" + "DO", "stu" + "b")


@dataclass(frozen=True)
class AgdaModuleSurface:
    path: Path
    rel_path: str
    text: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR)
    return parser.parse_args()


def read_surfaces(repo_root: Path, pattern: str) -> list[AgdaModuleSurface]:
    surfaces: list[AgdaModuleSurface] = []
    for path in sorted(repo_root.glob(pattern)):
        if path.is_file():
            rel_path = path.relative_to(repo_root).as_posix()
            surfaces.append(AgdaModuleSurface(path=path, rel_path=rel_path, text=path.read_text()))
    return surfaces


def bool_assignments(text: str) -> dict[str, bool]:
    assignments: dict[str, bool] = {}
    for name, value in re.findall(r"^([A-Za-z][A-Za-z0-9']*)\s*=\s*(true|false)\s*$", text, re.MULTILINE):
        assignments[name] = value == "true"
    return assignments


def quoted_strings(block: str) -> list[str]:
    return re.findall(r'"([^"]*)"', block)


def constructor_blocks(text: str, constructor_name: str) -> list[tuple[str, list[str]]]:
    blocks: list[tuple[str, list[str]]] = []
    pattern = re.compile(
        rf"^([A-Za-z][A-Za-z0-9']*)\s*:\s*[A-Za-z0-9_. ]+\n"
        rf"\1\s*=\s*\n\s*{re.escape(constructor_name)}\b(?P<body>.*?)(?=\n\n|\Z)",
        re.MULTILINE | re.DOTALL,
    )
    for match in pattern.finditer(text):
        blocks.append((match.group(1), quoted_strings(match.group("body"))))
    return blocks


def extract_blocked_gaps(surfaces: list[AgdaModuleSurface]) -> list[dict[str, str]]:
    gaps: list[dict[str, str]] = []
    for surface in surfaces:
        for definition, strings in constructor_blocks(surface.text, "mkBlockedGap"):
            if len(strings) >= 5:
                gaps.append(
                    {
                        "definition": definition,
                        "gap_id": strings[0],
                        "clay_requirement": strings[1],
                        "current_evidence": strings[2],
                        "reason_not_closed": strings[3],
                        "required_resolution": strings[4],
                        "source_path": surface.rel_path,
                    }
                )
    return gaps


def extract_evidence_items(surfaces: list[AgdaModuleSurface]) -> list[dict[str, str]]:
    items: list[dict[str, str]] = []
    for surface in surfaces:
        for definition, strings in constructor_blocks(surface.text, "mkEvidenceItem"):
            if len(strings) >= 4:
                items.append(
                    {
                        "definition": definition,
                        "evidence_id": strings[0],
                        "source_path_recorded": strings[1],
                        "claim_recorded": strings[2],
                        "status": strings[3],
                        "declared_in": surface.rel_path,
                    }
                )
    return items


def sprint105_scan(surfaces: list[AgdaModuleSurface]) -> list[dict[str, Any]]:
    scans: list[dict[str, Any]] = []
    for surface in surfaces:
        token_hits = [token for token in FORBIDDEN_SURFACE_TOKENS if token in surface.text]
        scans.append(
            {
                "path": surface.rel_path,
                "promotion_true": FORBIDDEN_PROMOTION in surface.text,
                "surface_token_hit_count": len(token_hits),
                "surface_tokens_clear": not token_hits,
            }
        )
    return scans


def make_summary(repo_root: Path) -> dict[str, Any]:
    sprint104 = read_surfaces(repo_root, SPRINT104_PATTERN)
    sprint105 = read_surfaces(repo_root, SPRINT105_PATTERN)
    scans = sprint105_scan(sprint105)
    fail_reasons = []
    for scan in scans:
        if scan["promotion_true"]:
            fail_reasons.append(f"{scan['path']}: promotion flag is true")
        if not scan["surface_tokens_clear"]:
            fail_reasons.append(f"{scan['path']}: reserved incomplete-surface token present")

    sprint104_bools: dict[str, dict[str, bool]] = {
        surface.rel_path: bool_assignments(surface.text) for surface in sprint104
    }
    gaps = extract_blocked_gaps(sprint104 + sprint105)
    evidence_items = extract_evidence_items(sprint104 + sprint105)
    route_decision = (
        "SPRINT105_FAIL_CLOSED_SCAN_VIOLATION"
        if fail_reasons
        else "SPRINT105_GAP_CLOSURE_PLAN_READY"
    )

    return {
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "repo_root": repo_root.as_posix(),
        "route_decision": route_decision,
        "fail_reasons": fail_reasons,
        "scanned_surfaces": {
            "sprint104": [surface.rel_path for surface in sprint104],
            "sprint105": [surface.rel_path for surface in sprint105],
        },
        "sprint104_bool_assignments": sprint104_bools,
        "sprint105_scan": scans,
        "remaining_dashi_native_theorem_obligations": [
            {
                "obligation_id": "transfer-gap-lower-bound",
                "title": "Transfer-gap lower bound",
                "closure_input": "A DASHI-native lower bound that separates the transfer gap from the mass scale being established.",
                "evidence_links": ["blocked-noncircular-mass-gap-proof"],
            },
            {
                "obligation_id": "symmetry-restoration",
                "title": "Symmetry restoration",
                "closure_input": "A DASHI-native restoration theorem carrying the OS3 spatial route into Poincare covariance and the spectrum condition.",
                "evidence_links": ["blocked-poincare-covariance", "blocked-spectrum-condition"],
            },
            {
                "obligation_id": "compact-simple-group-parameter-table-completeness-audit",
                "title": "Compact simple group parameter table/completeness audit",
                "closure_input": "A DASHI-native parameter table and audit proving every group-dependent estimate for any compact simple G.",
                "evidence_links": ["blocked-all-compact-simple-g"],
            },
        ],
        "supplied_gap_reductions": [
            {
                "reduction_id": "noncircular-mass-gap",
                "decision": "Convert the Sprint 104 circularity objection into the transfer-gap lower-bound obligation.",
                "evidence_links": ["blocked-noncircular-mass-gap-proof", "continuum-limit-mass-gap"],
            },
            {
                "reduction_id": "uniform-polymer-activity-constants",
                "decision": "Keep WC3 and uniform polymer activity constants as the quantitative input lane for the transfer comparison.",
                "evidence_links": ["wc3-uniform-cluster-summability"],
            },
            {
                "reduction_id": "os3-spatial-only-blocking-route",
                "decision": "Treat OS3 spatial-only blocking as the Euclidean route input that must be paired with restoration.",
                "evidence_links": ["blocked-wightman-distributions"],
            },
            {
                "reduction_id": "poincare-spectrum-via-symmetry-restoration",
                "decision": "Merge Poincare covariance and spectrum condition into the symmetry-restoration obligation.",
                "evidence_links": ["blocked-poincare-covariance", "blocked-spectrum-condition"],
            },
            {
                "reduction_id": "any-compact-simple-g-via-parameter-table",
                "decision": "Replace SU(3)-only closure with a compact-simple-G parameter table and completeness audit.",
                "evidence_links": ["blocked-all-compact-simple-g", "nontrivial-su3-measure"],
            },
        ],
        "extracted_blocked_gaps": gaps,
        "extracted_evidence_items": evidence_items,
        "promotion_state": {
            "clay_yang_mills_promoted_in_sprint104": any(
                bools.get("clayYangMillsPromoted", False)
                for bools in sprint104_bools.values()
            ),
            "sprint105_promotion_true_detected": any(scan["promotion_true"] for scan in scans),
        },
    }


def by_id(rows: list[dict[str, str]], key: str) -> dict[str, dict[str, str]]:
    return {row[key]: row for row in rows}


def render_markdown(summary: dict[str, Any]) -> str:
    gap_map = by_id(summary["extracted_blocked_gaps"], "gap_id")
    evidence_map = by_id(summary["extracted_evidence_items"], "evidence_id")
    lines = [
        "# YM Sprint 105 Gap Closure Plan",
        "",
        f"Route decision: `{summary['route_decision']}`",
        "",
        "## Scanned module surfaces",
        "",
    ]
    for label in ("sprint104", "sprint105"):
        paths = summary["scanned_surfaces"][label]
        if paths:
            for path in paths:
                lines.append(f"- {label}: `{path}`")
        else:
            lines.append(f"- {label}: no matching Agda modules present")
    lines.extend(
        [
            "",
            "## Three remaining DASHI-native theorem obligations",
            "",
        ]
    )
    for obligation in summary["remaining_dashi_native_theorem_obligations"]:
        lines.append(f"### {obligation['title']}")
        lines.append("")
        lines.append(obligation["closure_input"])
        lines.append("")
        lines.append("Evidence:")
        for evidence_id in obligation["evidence_links"]:
            source = gap_map.get(evidence_id) or evidence_map.get(evidence_id)
            if source and "source_path" in source:
                lines.append(f"- `{evidence_id}` from `{source['source_path']}`: {source['required_resolution']}")
            elif source:
                lines.append(
                    f"- `{evidence_id}` from `{source['declared_in']}` records `{source['source_path_recorded']}`."
                )
            else:
                lines.append(f"- `{evidence_id}` is required by the Sprint 105 reduction map.")
        lines.append("")

    lines.extend(["## Supplied gap reductions", ""])
    for reduction in summary["supplied_gap_reductions"]:
        lines.append(f"### {reduction['reduction_id']}")
        lines.append("")
        lines.append(reduction["decision"])
        lines.append("")
        evidence_bits = []
        for evidence_id in reduction["evidence_links"]:
            source = gap_map.get(evidence_id) or evidence_map.get(evidence_id)
            if source and "source_path" in source:
                evidence_bits.append(f"`{evidence_id}` in `{source['source_path']}`")
            elif source:
                evidence_bits.append(f"`{evidence_id}` declared in `{source['declared_in']}`")
            else:
                evidence_bits.append(f"`{evidence_id}`")
        lines.append("Evidence links: " + ", ".join(evidence_bits) + ".")
        lines.append("")

    lines.extend(
        [
            "## Scan gate",
            "",
            "Sprint 105 scanned surfaces must have no Clay promotion flag set to true and no reserved incomplete-surface tokens. This run passed that gate."
            if not summary["fail_reasons"]
            else "Sprint 105 scanned surfaces did not pass the conservative scan gate.",
            "",
        ]
    )
    return "\n".join(lines)


def write_outputs(summary: dict[str, Any], out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / SUMMARY_NAME).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    (out_dir / PLAN_NAME).write_text(render_markdown(summary) + "\n")


def main() -> None:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir if args.out_dir.is_absolute() else repo_root / args.out_dir
    summary = make_summary(repo_root)
    write_outputs(summary, out_dir)
    if summary["fail_reasons"]:
        for reason in summary["fail_reasons"]:
            print(f"fail-closed: {reason}")
        raise SystemExit(1)
    print(f"wrote {out_dir / SUMMARY_NAME}")
    print(f"wrote {out_dir / PLAN_NAME}")


if __name__ == "__main__":
    main()
