#!/usr/bin/env python3
"""Audit Agda context supplied by textually-unused historical imports.

This is a repair triage tool, not a proof of removability.  It follows the
existing import graph and flags source/transitive features that can affect
scope or elaboration even when no declaration name is visibly referenced.
"""

from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict, deque
from pathlib import Path

try:
    from scripts.agda_import_cone import parse_agda_file, strip_agda_comments
except ImportError:
    from agda_import_cone import parse_agda_file, strip_agda_comments


FEATURES = {
    "instance": re.compile(r"^\s*instance\b", re.MULTILINE),
    "public-import": re.compile(r"^\s*(?:open\s+)?import\s+.*\bpublic\b", re.MULTILINE),
    "operator-fixity": re.compile(r"^\s*infix(?:l|r)?\b", re.MULTILINE),
    "syntax-macro": re.compile(r"^\s*(?:syntax|macro)\b", re.MULTILINE),
    "postulate": re.compile(r"^\s*postulate\b", re.MULTILINE),
    "module-parameter": re.compile(r"^\s*module\s+[^ ]+\s*\{", re.MULTILINE),
}


def feature_names(path: Path) -> list[str]:
    text = strip_agda_comments(path.read_text(encoding="utf-8"))
    return sorted(name for name, pattern in FEATURES.items() if pattern.search(text))


def build_audit(repo_root: Path, ledger: dict, plan: dict) -> dict:
    records = {}
    for row in ledger["modules"]:
        path = repo_root / row["path"]
        if path.is_file():
            records[row["module"]] = parse_agda_file(path, repo_root)

    feature_cache: dict[str, list[str]] = {}
    closure_cache: dict[str, set[str]] = {}

    def closure(module: str) -> set[str]:
        if module in closure_cache:
            return closure_cache[module]
        seen = set()
        queue = deque([module])
        while queue:
            current = queue.popleft()
            if current in seen:
                continue
            seen.add(current)
            record = records.get(current)
            if record:
                queue.extend(imported for imported in record.imports if imported in records)
        closure_cache[module] = seen
        return seen

    rows = []
    for item in plan["rows"]:
        if item["status"] != "unused-import-remove-or-recheck":
            continue
        source = item["historical_module"]
        transitive = closure(source)
        direct_features = feature_cache.setdefault(
            source, feature_names(repo_root / next(row["path"] for row in ledger["modules"] if row["module"] == source))
        )
        transitive_features = sorted({
            feature for module in transitive
            for feature in feature_names(records[module].path)
        })
        reasons = []
        if item.get("import_alias"):
            reasons.append("qualified-alias-context")
        if direct_features:
            reasons.append("direct-source-feature")
        if transitive_features:
            reasons.append("transitive-source-feature")
        if not reasons:
            reasons.append("unknown-elaboration-context")
        rows.append({
            "consumer": item["consumer"],
            "consumer_path": item["consumer_path"],
            "line": item["line"],
            "historical_module": source,
            "direct_features": direct_features,
            "transitive_features": transitive_features,
            "transitive_module_count": len(transitive),
            "repair_reasons": reasons,
            "status": "requires-Agda-probe",
            "verification_command": "DASHI_NO_TMUX=1 scripts/run_agda29_parallel_check.sh " + item["consumer_path"],
        })
    counts = defaultdict(int)
    for row in rows:
        for reason in row["repair_reasons"]:
            counts[reason] += 1
    return {
        "schema_version": 1,
        "purpose": "Agda-level context repair triage for textually-unused historical imports",
        "candidate_count": len(rows),
        "reason_counts": dict(sorted(counts.items())),
        "rows": rows,
        "deletion_authorized": False,
        "policy": "feature detection narrows probes but never authorizes removal; only a sanctioned Agda probe can do that",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--ledger", type=Path, default=Path(".dashi/round-stranded/ym-consolidation-ledger.json"))
    parser.add_argument("--plan", type=Path, default=Path(".dashi/round-stranded/ym-migration-plan.json"))
    parser.add_argument("--output", type=Path, default=Path(".dashi/round-stranded/ym-context-audit.json"))
    args = parser.parse_args()
    root = args.repo_root.resolve()
    audit = build_audit(
        root,
        json.loads((root / args.ledger).read_text(encoding="utf-8")),
        json.loads((root / args.plan).read_text(encoding="utf-8")),
    )
    output = root / args.output
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({
        "candidate_count": audit["candidate_count"],
        "reason_counts": audit["reason_counts"],
        "deletion_authorized": audit["deletion_authorized"],
        "output": str(output),
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
