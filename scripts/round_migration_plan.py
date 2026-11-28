#!/usr/bin/env python3
"""Generate a fail-closed import-rewrite plan from reviewed declaration mappings.

The mapping file is the only semantic input.  This tool automates the
mechanical work around it: import parsing, declaration-use classification,
rewrite eligibility, dependency ordering, and deletion gates.  It never edits
Agda files and never treats a name or signature match as a mapping.
"""

from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict, deque
from pathlib import Path

try:
    from scripts.agda_import_cone import strip_agda_comments
except ImportError:
    from agda_import_cone import strip_agda_comments


ROUND_RE = re.compile(r"(?:^|\.)(?:R\d+|Round\d+)(?:[^.]|$)")
IMPORT_RE = re.compile(
    r"^(?P<indent>\s*)(?P<open>open\s+)?import\s+"
    r"(?P<module>[A-Za-z0-9_.]+)(?P<rest>.*)$"
)
USING_RE = re.compile(r"\busing\s*\((?P<names>[^)]*)\)")
NAME_RE = re.compile(r"[A-Za-z][A-Za-z0-9_']*")
DECL_RE = re.compile(
    r"^[ \t]*(?:([A-Za-z][A-Za-z0-9_']*)[ \t]*:|"
    r"(?:record|data|postulate)[ \t]+([A-Za-z][A-Za-z0-9_']*))",
    re.MULTILINE,
)


def historical(module: str) -> bool:
    return bool(ROUND_RE.search(module))


def mapping_for_module(mapping: dict[str, str], module: str) -> dict[str, tuple[str, str]]:
    result = {}
    prefix = module + "::"
    for source, target in mapping.items():
        if source.startswith(prefix) and "::" in target:
            result[source[len(prefix):]] = tuple(target.split("::", 1))
    return result


def imported_names(rest: str) -> tuple[str, ...] | None:
    match = USING_RE.search(rest)
    if not match:
        return None
    return tuple(sorted(set(NAME_RE.findall(match.group("names")))))


def source_mentions(text: str, names: tuple[str, ...]) -> tuple[str, ...]:
    stripped = strip_agda_comments(text)
    stripped = "\n".join(
        line for line in stripped.splitlines()
        if not IMPORT_RE.match(line) and not line.lstrip().startswith("module ")
    )
    return tuple(sorted(name for name in names if re.search(rf"\b{re.escape(name)}\b", stripped)))


def declared_names(path: Path) -> tuple[str, ...]:
    if not path.is_file():
        return ()
    names = set()
    for first, second in DECL_RE.findall(strip_agda_comments(path.read_text(encoding="utf-8"))):
        names.add(first or second)
    return tuple(sorted(names))


def parse_import_lines(path: Path) -> list[dict]:
    text = path.read_text(encoding="utf-8")
    lines = []
    for number, line in enumerate(strip_agda_comments(text).splitlines(), 1):
        match = IMPORT_RE.match(line)
        if match:
            lines.append({
                "line": number,
                "module": match.group("module"),
                "open": bool(match.group("open")),
                "alias": (re.search(r"\bas\s+([A-Za-z][A-Za-z0-9_']*)", match.group("rest")) or [None, None])[1],
                "names": imported_names(match.group("rest")),
            })
    return lines


def module_path(repo_root: Path, module: str) -> Path:
    return repo_root / Path(*module.split(".")).with_suffix(".agda")


def build_plan(repo_root: Path, ledger: dict, mapping: dict[str, str]) -> dict:
    rows = []
    touched_consumers = set()
    importer_modules = defaultdict(set)
    historical_paths = {
        row["module"]: repo_root / row["path"]
        for row in ledger["modules"]
    }

    for historical_row in ledger["modules"]:
        for consumer in historical_row.get("nonhistorical_importers", []):
            importer_modules[consumer].add(historical_row["module"])

    for consumer, expected_sources in sorted(importer_modules.items()):
        path = module_path(repo_root, consumer)
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8")
        for item in parse_import_lines(path):
            source = item["module"]
            if source not in expected_sources:
                continue
            touched_consumers.add(consumer)
            historical_names = declared_names(historical_paths[source])
            used_historical_names = source_mentions(text, historical_names)
            alias = item["alias"]
            if alias:
                qualified = tuple(
                    name for name in historical_names
                    if re.search(rf"\b{re.escape(alias)}\s*\.\s*{re.escape(name)}\b", text)
                )
                used_historical_names = tuple(sorted(set(used_historical_names) | set(qualified)))
            unused_historical_names = tuple(sorted(set(historical_names) - set(used_historical_names)))
            by_name = mapping_for_module(mapping, source)
            names = item["names"]
            if names is None:
                used = used_historical_names
                missing = sorted(set(used) - set(by_name))
                targets = {by_name[name][0] for name in used if name in by_name}
                if not used:
                    status = "unused-import-remove-or-recheck"
                elif missing:
                    status = "mapping-incomplete"
                elif len(targets) != 1:
                    status = "multiple-canonical-targets"
                else:
                    status = "rewrite-ready"
            else:
                used = source_mentions(text, names)
                missing = sorted(set(used) - set(by_name))
                targets = {by_name[name][0] for name in used if name in by_name}
                if not used:
                    status = "unused-import-remove-or-recheck"
                elif missing:
                    status = "mapping-incomplete"
                elif len(targets) != 1:
                    status = "multiple-canonical-targets"
                else:
                    status = "rewrite-ready"
            rows.append({
                "consumer": consumer,
                "consumer_path": str(path.relative_to(repo_root)),
                "line": item["line"],
                "historical_module": source,
                "open_import": item["open"],
                "import_alias": alias,
                "imported_names": list(names) if names is not None else None,
                "historical_declared_names": list(historical_names),
                "used_names": list(used),
                "unused_historical_names": list(unused_historical_names),
                "mapped_declarations": {
                    name: "::".join(by_name[name]) for name in used if name in by_name
                },
                "status": status,
            })
    return {
        "schema_version": 1,
        "purpose": "mechanical import migration plan from reviewed declaration mappings",
        "mapping_count": len(mapping),
        "direct_historical_import_edge_count": len(rows),
        "consumer_count": len(touched_consumers),
        "status_counts": {
            status: sum(row["status"] == status for row in rows)
            for status in sorted({row["status"] for row in rows})
        },
        "rows": rows,
        "dependency_order": sorted(touched_consumers),
        "deletion_policy": "no deletion is authorized; only rewrite-ready rows may be mechanically patched after review",
    }


def apply_unused_import_removals(repo_root: Path, plan: dict) -> int:
    """Remove only plan rows proven to use no historical declaration names."""
    by_path: dict[Path, list[dict]] = defaultdict(list)
    for row in plan["rows"]:
        if row["status"] == "unused-import-remove-or-recheck":
            by_path[repo_root / row["consumer_path"]].append(row)
    changed = 0
    for path, rows in by_path.items():
        original = path.read_text(encoding="utf-8").splitlines(keepends=True)
        remove_lines = {row["line"] for row in rows}
        kept = []
        for number, line in enumerate(original, 1):
            if number in remove_lines and any(
                row["historical_module"] in line for row in rows if row["line"] == number
            ):
                changed += 1
                continue
            kept.append(line)
        if len(kept) != len(original):
            path.write_text("".join(kept), encoding="utf-8")
    return changed


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--ledger", type=Path, default=Path(".dashi/round-stranded/ym-consolidation-ledger.json"))
    parser.add_argument("--mapping", type=Path, default=Path("config/ym-round-consolidation-mapping.json"))
    parser.add_argument("--json-output", type=Path, default=Path(".dashi/round-stranded/ym-migration-plan.json"))
    parser.add_argument(
        "--apply-unused-import-removals",
        action="store_true",
        help="remove only exact rows classified as unused-import-remove-or-recheck",
    )
    args = parser.parse_args()
    root = args.repo_root.resolve()
    ledger = json.loads((root / args.ledger).read_text(encoding="utf-8"))
    mapping_doc = json.loads((root / args.mapping).read_text(encoding="utf-8"))
    mapping = mapping_doc.get("declarations", mapping_doc)
    plan = build_plan(root, ledger, mapping)
    applied = 0
    if args.apply_unused_import_removals:
        applied = apply_unused_import_removals(root, plan)
    output = root / args.json_output
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(plan, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({
        "mapping_count": plan["mapping_count"],
        "direct_historical_import_edge_count": plan["direct_historical_import_edge_count"],
        "consumer_count": plan["consumer_count"],
        "status_counts": plan["status_counts"],
        "applied_unused_import_removals": applied,
        "output": str(output),
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
