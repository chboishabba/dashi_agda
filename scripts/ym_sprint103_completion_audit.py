#!/usr/bin/env python3
"""Sprint 103 YM completion receipt audit.

The audit checks the receipt layer only.  It does not treat external
acceptance as locally constructible proof evidence, and it fail-closes Clay YM
promotion if any Sprint103 module promotes it.
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any


DEFAULT_OUT_DIR = Path("outputs/ym_sprint103_completion")
SUMMARY_NAME = "ym_sprint103_completion_summary.json"
SPRINT103_GLOB = "DASHI/Physics/Closure/*Sprint103*.agda"


@dataclass(frozen=True)
class MathItem:
    item_id: str
    anchor: str
    description: str


MATH_ITEMS: tuple[MathItem, ...] = (
    MathItem(
        "balaban_cmp98_local_oscillation",
        "BalabanCMP98LocalOscillationBound",
        "CMP98 local oscillation bound",
    ),
    MathItem(
        "balaban_cmp98_kernel_probability",
        "BalabanCMP98AveragingKernelIsProbability",
        "CMP98 averaging kernel probability",
    ),
    MathItem(
        "balaban_cmp116_polymer_mass",
        "BalabanCMP116PolymerMassBound",
        "CMP116 polymer mass bound",
    ),
    MathItem(
        "gauge_covariant_dobrushin_comparison",
        "GaugeCovariantDobrushinComparison",
        "gauge-covariant Dobrushin comparison",
    ),
    MathItem(
        "uniform_polymer_activity_from_dobrushin",
        "UniformPolymerActivityFromDobrushin",
        "uniform polymer activity from Dobrushin",
    ),
    MathItem(
        "wc3_uniform_cluster_summability",
        "WC3UniformClusterSummability",
        "WC3 uniform cluster summability",
    ),
    MathItem(
        "continuum_limit_mass_gap",
        "ContinuumLimitMassGap",
        "continuum-limit mass gap",
    ),
    MathItem(
        "nontrivial_4d_su3_yang_mills_measure",
        "Nontrivial4DSU3YangMillsMeasure",
        "nontrivial 4D SU(3) Yang-Mills measure",
    ),
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR)
    return parser.parse_args()


def read_sprint103_modules(repo_root: Path) -> dict[str, str]:
    modules: dict[str, str] = {}
    for path in sorted(repo_root.glob(SPRINT103_GLOB)):
        if path.is_file():
            modules[str(path.relative_to(repo_root))] = path.read_text()
    return modules


def _top_level_chunks(text: str) -> list[tuple[str, str]]:
    matches = list(re.finditer(r"(?m)^(record\s+[A-Za-z][A-Za-z0-9_']*Receipt[A-Za-z0-9_']*.*)$", text))
    chunks: list[tuple[str, str]] = []
    for index, match in enumerate(matches):
        start = match.start()
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        chunks.append((match.group(1), text[start:end]))
    return chunks


def non_empty_receipt_records(text: str) -> set[str]:
    records: set[str] = set()
    for header, chunk in _top_level_chunks(text):
        name_match = re.search(r"record\s+([A-Za-z][A-Za-z0-9_']*Receipt[A-Za-z0-9_']*)", header)
        if name_match is None:
            continue
        name = name_match.group(1)
        has_fields = re.search(r"(?m)^\s*field\s*$", chunk) is not None
        has_named_field = re.search(r"(?m)^\s{4,}[A-Za-z][A-Za-z0-9_']*\s*:", chunk) is not None
        if has_fields and has_named_field:
            records.add(name)
    return records


def inhabited_receipt_records(text: str) -> set[str]:
    inhabited: set[str] = set()
    for record_name in non_empty_receipt_records(text):
        typed_value = re.compile(
            rf"(?ms)^([A-Za-z][A-Za-z0-9_']*)\s*:\s*(?:\n\s*)?"
            rf"{re.escape(record_name)}\b.*?^\1\s*="
        )
        if typed_value.search(text):
            inhabited.add(record_name)
    return inhabited


def module_receipt_index(modules: dict[str, str]) -> dict[str, list[str]]:
    return {
        path: sorted(inhabited_receipt_records(text))
        for path, text in modules.items()
    }


def item_statuses(
    modules: dict[str, str],
    receipts_by_module: dict[str, list[str]],
) -> list[dict[str, Any]]:
    statuses: list[dict[str, Any]] = []
    for item in MATH_ITEMS:
        containing_paths = [
            path for path, text in modules.items() if item.anchor in text
        ]
        inhabited_records = sorted(
            {
                record
                for path in containing_paths
                for record in receipts_by_module.get(path, [])
            }
        )
        statuses.append(
            {
                "item_id": item.item_id,
                "anchor": item.anchor,
                "description": item.description,
                "represented_in_sprint103_module": bool(containing_paths),
                "sprint103_modules": containing_paths,
                "inhabited_non_empty_receipt_records": inhabited_records,
                "formal_receipt_completed": bool(containing_paths)
                and bool(inhabited_records),
            }
        )
    return statuses


def clay_promotion_status(modules: dict[str, str]) -> dict[str, Any]:
    joined = "\n".join(modules.values())
    true_hits = sorted(
        path
        for path, text in modules.items()
        if re.search(r"(?m)^\s*clayYangMillsPromoted\s*=\s*true\s*$", text)
    )
    false_hits = sorted(
        path
        for path, text in modules.items()
        if re.search(r"(?m)^\s*clayYangMillsPromoted\s*=\s*false\s*$", text)
    )
    return {
        "clayYangMillsPromoted": False if not true_hits else True,
        "explicit_false_present": bool(false_hits),
        "true_promotion_modules": true_hits,
        "false_promotion_modules": false_hits,
        "no_clay_promotion": bool(false_hits) and not true_hits,
        "text_mentions_promotion_flag": "clayYangMillsPromoted" in joined,
    }


def external_acceptance_status(modules: dict[str, str]) -> dict[str, Any]:
    true_hits = sorted(
        path
        for path, text in modules.items()
        if re.search(r"(?m)^\s*externalAcceptanceTokenAvailable\s*=\s*true\s*$", text)
    )
    false_hits = sorted(
        path
        for path, text in modules.items()
        if re.search(r"(?m)^\s*externalAcceptanceTokenAvailable\s*=\s*false\s*$", text)
    )
    return {
        "distinguished_from_formal_receipt_completion": True,
        "external_acceptance_token_available_in_repo": bool(true_hits),
        "external_acceptance_token_explicitly_unavailable": bool(false_hits)
        and not true_hits,
        "self_issuable_by_repo": False,
        "true_acceptance_modules": true_hits,
        "false_acceptance_modules": false_hits,
        "boundary_statement": (
            "External acceptance is a review/governance boundary and is not "
            "counted as formal Sprint103 receipt completion."
        ),
    }


def build_summary(repo_root: Path) -> dict[str, Any]:
    modules = read_sprint103_modules(repo_root)
    receipts_by_module = module_receipt_index(modules)
    items = item_statuses(modules, receipts_by_module)
    completed_count = sum(1 for item in items if item["formal_receipt_completed"])
    clay = clay_promotion_status(modules)
    external = external_acceptance_status(modules)
    all_items_completed = completed_count == len(MATH_ITEMS)

    return {
        "sprint": "103-completion",
        "repo_root": str(repo_root.resolve()),
        "sprint103_module_count": len(modules),
        "sprint103_modules": sorted(modules),
        "expected_math_item_count": len(MATH_ITEMS),
        "formal_receipt_completed_count": completed_count,
        "all_eight_user_supplied_math_items_formally_receipted": all_items_completed,
        "math_items": items,
        "inhabited_receipt_records_by_module": receipts_by_module,
        "formal_receipt_completion": {
            "complete": all_items_completed,
            "basis": (
                "Exact item anchors must occur in Sprint103 modules that also "
                "contain at least one inhabited non-empty Receipt record."
            ),
        },
        "external_acceptance": external,
        "clay_promotion": clay,
        "clayYangMillsPromoted": clay["clayYangMillsPromoted"],
        "route_decision": (
            "SPRINT103_FORMAL_RECEIPTS_COMPLETE_NO_EXTERNAL_ACCEPTANCE_NO_CLAY_PROMOTION"
            if all_items_completed
            and external["distinguished_from_formal_receipt_completion"]
            and not external["external_acceptance_token_available_in_repo"]
            and clay["no_clay_promotion"]
            else "SPRINT103_AUDIT_FAIL_CLOSED"
        ),
    }


def write_outputs(summary: dict[str, Any], out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / SUMMARY_NAME).write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n"
    )


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = repo_root / out_dir
    summary = build_summary(repo_root)
    write_outputs(summary, out_dir)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
