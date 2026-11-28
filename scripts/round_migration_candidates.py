#!/usr/bin/env python3
"""Generate declaration-level migration candidates from the YM package JSONL.

This is the automated discovery stage of the migration engine.  It streams the
precomputed package file and reports historical declarations for which the
package extractor already found a non-Round owner.  It never edits Agda,
populates the canonical mapping, or authorizes deletion.

Candidate classes are deliberately fail-closed:

* ``exact-selected-owner``: the package selected an owner and exactly one
  declaration in that owner has the same non-empty signature and body hashes;
* ``exact-unique``: exactly one non-Round declaration has both hashes;
* ``exact-ambiguous``: several declarations share both hashes (often generic
  proof-level material);
* ``signature-only``: only a signature match exists;
* ``unresolved``: no non-Round declaration-level evidence exists.

The output is a review surface for the mapping file, not the mapping file.
"""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Iterable


# Historical module names commonly embed ``RoundNNN`` inside a family name,
# e.g. ``Balaban...Round410Exact``; unlike import-token parsing, this surface
# must not require a dot boundary.
ROUND_RE = re.compile(r"(?:R\d+|Round\d+)")


def historical(module: str) -> bool:
    return bool(ROUND_RE.search(module))


def nonempty(value: Any) -> bool:
    return isinstance(value, str) and bool(value)


def exact_matches(declaration: dict[str, Any], matches: list[dict[str, Any]]) -> list[dict[str, str]]:
    signature = declaration.get("signature_sha256")
    body = declaration.get("body_sha256")
    if not nonempty(signature) or not nonempty(body):
        return []
    result = []
    seen = set()
    for match in matches:
        if match.get("signature_sha256") != signature or match.get("body_sha256") != body:
            continue
        module = match.get("module")
        name = match.get("name")
        if not module or not name or historical(module):
            continue
        key = (module, name)
        if key not in seen:
            result.append({
                "module": module,
                "name": name,
                "symbol_id": match.get("symbol_id", f"{module}.{name}"),
            })
            seen.add(key)
    return sorted(result, key=lambda row: (row["module"], row["name"]))


def signature_matches(declaration: dict[str, Any], matches: list[dict[str, Any]]) -> list[dict[str, str]]:
    signature = declaration.get("signature_sha256")
    if not nonempty(signature):
        return []
    result = []
    seen = set()
    for match in matches:
        if match.get("signature_sha256") != signature:
            continue
        module = match.get("module")
        name = match.get("name")
        if not module or not name or historical(module):
            continue
        key = (module, name)
        if key not in seen:
            result.append({
                "module": module,
                "name": name,
                "symbol_id": match.get("symbol_id", f"{module}.{name}"),
                "body_sha256": match.get("body_sha256", ""),
            })
            seen.add(key)
    return sorted(result, key=lambda row: (row["module"], row["name"]))


def classify(declaration: dict[str, Any], package: dict[str, Any]) -> tuple[str, list[dict[str, str]]]:
    matches = package.get("nonround_matches", [])
    exact = exact_matches(declaration, matches)
    selected = package.get("selected_canonical_owner")
    selected_exact = [row for row in exact if row["module"] == selected]
    if selected and len(selected_exact) == 1:
        return "exact-selected-owner", selected_exact
    if len(exact) == 1:
        return "exact-unique", exact
    if len(exact) > 1:
        return "exact-ambiguous", exact
    signatures = signature_matches(declaration, matches)
    if signatures:
        return "signature-only", signatures
    return "unresolved", []


def iter_candidates(source: Path) -> Iterable[dict[str, Any]]:
    with source.open(encoding="utf-8") as stream:
        for line in stream:
            if not line.strip():
                continue
            package = json.loads(line)
            for declaration in package.get("declarations", []):
                module = declaration.get("module", "")
                if not historical(module):
                    continue
                status, candidates = classify(declaration, package)
                yield {
                    "source": declaration.get("symbol_id", f"{module}.{declaration.get('name', '')}"),
                    "module": module,
                    "name": declaration.get("name", ""),
                    "package_id": package.get("package_id", ""),
                    "archive_status": package.get("archive_status"),
                    "disposition": package.get("disposition"),
                    "selected_canonical_owner": package.get("selected_canonical_owner"),
                    "signature_sha256": declaration.get("signature_sha256", ""),
                    "body_sha256": declaration.get("body_sha256", ""),
                    "status": status,
                    "candidates": candidates,
                    "unresolved_residuals": sorted(set(package.get("unresolved_residuals", []))),
                }


def build_report(source: Path, terminal_recipients: set[str] | None = None,
                 module_context: dict[str, dict[str, Any]] | None = None) -> dict[str, Any]:
    rows = list(iter_candidates(source))
    counts = Counter(row["status"] for row in rows)
    module_context = module_context or {}
    for row in rows:
        context = module_context.get(row["module"], {})
        row["textually_used_by_live_consumer"] = row["name"] in set(context.get("used_names", []))
        row["live_reverse_consumer_count"] = context.get("live_reverse_consumer_count")
        row["direct_importer_count"] = context.get("direct_importer_count")
        row["migration_action"] = context.get("migration_action")
        if not module_context:
            row["migration_relevance"] = "unclassified"
        elif row["textually_used_by_live_consumer"]:
            row["migration_relevance"] = "live-declaration-use"
        elif row["live_reverse_consumer_count"]:
            row["migration_relevance"] = "live-module-context"
        else:
            row["migration_relevance"] = "no-live-consumer"
    mapping_ready = [
        row for row in rows
        if row["status"] in {"exact-selected-owner", "exact-unique"}
    ]
    for row in mapping_ready:
        target_module = row["candidates"][0]["module"]
        row["target_is_terminal_recipient"] = (
            terminal_recipients is None or target_module in terminal_recipients
        )
    terminal_ready = [row for row in mapping_ready if row["target_is_terminal_recipient"]]
    groups: dict[str, dict[str, Any]] = {}
    for row in rows:
        if row["status"] not in {"exact-ambiguous", "signature-only"}:
            continue
        if row["status"] == "exact-ambiguous":
            key = f"exact:{row['signature_sha256']}:{row['body_sha256']}"
        else:
            key = f"signature:{row['signature_sha256']}"
        group = groups.setdefault(key, {
            "key": key,
            "evidence": row["status"],
            "signature_sha256": row["signature_sha256"],
            "body_sha256": row["body_sha256"],
            "declaration_count": 0,
            "sources": [],
            "candidate_targets": set(),
        })
        group["declaration_count"] += 1
        group["sources"].append(row["source"])
        group["candidate_targets"].update(
            candidate["symbol_id"] for candidate in row["candidates"]
        )
    review_groups = []
    for group in groups.values():
        group["sources"] = sorted(group["sources"])
        group["candidate_targets"] = sorted(group["candidate_targets"])
        review_groups.append(group)
    review_groups.sort(key=lambda row: (-row["declaration_count"], row["key"]))
    return {
        "schema_version": 1,
        "purpose": "automated, fail-closed declaration mapping candidates",
        "source": str(source),
        "declaration_count": len(rows),
        "status_counts": dict(sorted(counts.items())),
        "migration_relevance_counts": dict(sorted(
            Counter(row["migration_relevance"] for row in rows).items()
        )),
        "mapping_candidate_count": len(mapping_ready),
        "terminal_mapping_candidate_count": len(terminal_ready),
        "review_group_count": len(review_groups),
        "review_groups": review_groups,
        "mapping_candidates": [
            {
                "source": row["source"],
                "target": row["candidates"][0]["symbol_id"],
                "evidence": row["status"],
                "package_id": row["package_id"],
                "target_is_terminal_recipient": row["target_is_terminal_recipient"],
            }
            for row in mapping_ready
        ],
        "rows": rows,
        "policy": {
            "candidates_are_not_mappings": True,
            "empty_hashes_excluded": True,
            "round_targets_forbidden": True,
            "generic_signature_matches_require_review": True,
            "deletion_authorized": False,
            "terminal_candidates_require_manifest_membership": terminal_recipients is not None,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=Path(".dashi/round-stranded/ym-packages.jsonl"))
    parser.add_argument("--ledger", type=Path, default=Path(".dashi/round-stranded/ym-consolidation-ledger.json"))
    parser.add_argument("--output", type=Path, default=Path(".dashi/round-stranded/ym-migration-candidates.json"))
    args = parser.parse_args()
    ledger = json.loads(args.ledger.read_text(encoding="utf-8")) if args.ledger.is_file() else {}
    plan_path = Path(".dashi/round-stranded/ym-migration-plan.json")
    plan = json.loads(plan_path.read_text(encoding="utf-8")) if plan_path.is_file() else {}
    context: dict[str, dict[str, Any]] = defaultdict(lambda: {
        "used_names": set(), "live_reverse_consumer_count": 0,
        "direct_importer_count": 0, "migration_action": None,
    })
    for row in ledger.get("modules", []):
        context[row["module"]]["live_reverse_consumer_count"] = len(
            row.get("reverse_cone_nonhistorical_consumers", [])
        )
        context[row["module"]]["direct_importer_count"] = len(
            row.get("nonhistorical_importers", [])
        )
        context[row["module"]]["migration_action"] = row.get("migration_action")
    for row in plan.get("rows", []):
        context[row["historical_module"]]["used_names"].update(row.get("used_names", []))
    report = build_report(args.source, set(ledger.get("terminal_recipients", [])), context)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({
        "declaration_count": report["declaration_count"],
        "status_counts": report["status_counts"],
        "migration_relevance_counts": report["migration_relevance_counts"],
        "mapping_candidate_count": report["mapping_candidate_count"],
        "terminal_mapping_candidate_count": report["terminal_mapping_candidate_count"],
        "output": str(args.output),
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
