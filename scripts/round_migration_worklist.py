#!/usr/bin/env python3
"""Turn the Round consolidation ledger into a reviewable migration worklist.

This is deliberately a planning tool.  It processes all historical modules in
the generated ledger, groups their reverse-cone consumers, and ranks existing
non-Round terminal modules by name overlap.  It never edits Agda files and
never writes a declaration mapping automatically: a candidate is evidence for
review, not a semantic equivalence claim.
"""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter, defaultdict
from pathlib import Path


GENERIC = {
    "agda", "exact", "validation", "source", "canonical", "clay", "round",
    "balaban", "yang", "mills", "physics", "dashi", "the", "and", "to",
    "from", "with", "for", "of", "on", "at", "by", "module", "route",
}


def tokens(name: str) -> set[str]:
    words = re.findall(r"[A-Z]+(?=[A-Z][a-z]|\d|$)|[A-Z]?[a-z]+|\d+", name)
    return {word.lower() for word in words if word.lower() not in GENERIC and not word.isdigit()}


def rank_targets(module: str, consumers: list[str], targets: list[str], limit: int = 12):
    source_tokens = tokens(module) | set().union(*(tokens(c) for c in consumers))
    ranked = []
    for target in targets:
        overlap = source_tokens & tokens(target)
        score = len(overlap)
        ranked.append({"module": target, "score": score, "shared_tokens": sorted(overlap)})
    ranked.sort(key=lambda row: (-row["score"], row["module"]))
    return ranked[:limit]


def build_worklist(ledger: dict) -> dict:
    terminal = set(ledger["terminal_recipients"])
    by_consumer: dict[str, dict] = defaultdict(lambda: {
        "historical_modules": [],
        "direct_imports": [],
        "needs_extraction": [],
    })
    historical = []
    for row in ledger["modules"]:
        consumers = sorted(set(row.get("reverse_cone_nonhistorical_consumers", [])))
        if not consumers:
            continue
        historical.append(row["module"])
        candidate_targets = [
            target for target in row.get("terminal_recipient_candidates", [])
            if target in terminal
        ]
        if not candidate_targets:
            candidate_targets = [
                target for target in row.get("preferred_canonical_targets", [])
                if target in terminal
            ]
        for consumer in consumers:
            entry = by_consumer[consumer]
            entry["historical_modules"].append(row["module"])
            if consumer in row.get("nonhistorical_importers", []):
                entry["direct_imports"].append(row["module"])
            if not candidate_targets:
                entry["needs_extraction"].append(row["module"])

    rows = []
    for consumer, entry in sorted(by_consumer.items()):
        historical_modules = sorted(set(entry["historical_modules"]))
        direct_imports = sorted(set(entry["direct_imports"]))
        extraction = sorted(set(entry["needs_extraction"]))
        candidate_pool = set()
        for module in historical_modules:
            source = next(row for row in ledger["modules"] if row["module"] == module)
            candidate_pool.update(source.get("terminal_recipient_candidates", []))
            candidate_pool.update(source.get("preferred_canonical_targets", []))
        candidate_pool &= terminal
        rows.append({
            "consumer": consumer,
            "historical_module_count": len(historical_modules),
            "historical_modules": historical_modules,
            "direct_historical_imports": direct_imports,
            "reverse_cone_only": sorted(set(historical_modules) - set(direct_imports)),
            "requires_declaration_extraction": extraction,
            "ranked_canonical_candidates": rank_targets(
                consumer, historical_modules, sorted(candidate_pool)
            ),
            "review_status": "needs-semantic-review",
        })

    return {
        "schema_version": 1,
        "purpose": "review live historical Round consumers before import rewrites",
        "source_ledger": ledger.get("repo_root", "") + "/.dashi/round-stranded/ym-consolidation-ledger.json",
        "historical_modules_with_live_consumers": len(historical),
        "live_consumer_count": len(rows),
        "historical_module_count_by_consumer": Counter(row["historical_module_count"] for row in rows),
        "rows": rows,
        "policy": {
            "candidates_are_not_mappings": True,
            "round_targets_forbidden": True,
            "rewrites_require_review_and_sanctioned_agda_check": True,
        },
    }


def write_markdown(worklist: dict, path: Path) -> None:
    lines = [
        "# YM Round migration worklist",
        "",
        "This is a generated review queue. It does not authorize rewrites or deletion.",
        "",
        f"- Historical modules with live consumers: **{worklist['historical_modules_with_live_consumers']}**",
        f"- Distinct live consumers: **{worklist['live_consumer_count']}**",
        "",
        "| Consumer | Historical inputs | Direct imports | Extraction cases | Top candidates |",
        "|---|---:|---:|---:|---|",
    ]
    for row in worklist["rows"]:
        candidates = ", ".join(
            f"{candidate['module']} ({candidate['score']})"
            for candidate in row["ranked_canonical_candidates"][:3]
        ) or "none"
        lines.append(
            f"| `{row['consumer']}` | {row['historical_module_count']} | "
            f"{len(row['direct_historical_imports'])} | "
            f"{len(row['requires_declaration_extraction'])} | {candidates} |"
        )
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--ledger",
        type=Path,
        default=Path(".dashi/round-stranded/ym-consolidation-ledger.json"),
    )
    parser.add_argument(
        "--json-output",
        type=Path,
        default=Path(".dashi/round-stranded/ym-migration-worklist.json"),
    )
    parser.add_argument(
        "--markdown-output",
        type=Path,
        default=Path(".dashi/round-stranded/ym-migration-worklist.md"),
    )
    args = parser.parse_args()
    ledger = json.loads(args.ledger.read_text(encoding="utf-8"))
    worklist = build_worklist(ledger)
    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(json.dumps(worklist, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(worklist, args.markdown_output)
    print(json.dumps({
        "historical_modules_with_live_consumers": worklist["historical_modules_with_live_consumers"],
        "live_consumer_count": worklist["live_consumer_count"],
        "json_output": str(args.json_output),
        "markdown_output": str(args.markdown_output),
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
