#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from collections import defaultdict
from pathlib import Path

from _stranded_common import (
    connect,
    decls_for_modules,
    family_of,
    is_round,
    load_import_graph,
    module_paths,
    stable_id,
)


def load_targets(path: Path) -> dict:
    cfg = json.loads(path.read_text(encoding="utf-8"))
    required = {
        "schema_version",
        "target_prefix",
        "seed_families",
        "candidate_positive_names",
        "status_count_names",
        "outputs",
    }
    missing = required - set(cfg)
    if missing:
        raise SystemExit(f"missing extraction config keys: {sorted(missing)}")
    return cfg


def build_round_graph(imports, modules):
    modules = set(modules)
    parents = defaultdict(set)
    children = defaultdict(set)
    for child in sorted(modules):
        for parent in imports.get(child, ()):
            if parent in modules and is_round(parent):
                parents[child].add(parent)
                children[parent].add(child)
    return parents, children


def _ancestors(start: str, parents) -> set[str]:
    seen: set[str] = set()
    stack = [start]
    while stack:
        module = stack.pop()
        if module in seen:
            continue
        seen.add(module)
        stack.extend(sorted(parents.get(module, ())))
    return seen


def _decl_dict(row) -> dict:
    return {
        "symbol_id": row["symbol_id"],
        "module": row["module"],
        "file": row["file"],
        "name": row["name"],
        "kind": row["kind"],
        "normalized_signature": row["normalized_signature"],
        "signature_sha256": row["signature_sha256"],
        "body_sha256": row["body_sha256"],
    }


def cluster_packages(conn, cfg: dict) -> list[dict]:
    paths = module_paths(conn)
    imports, _ = load_import_graph(conn)
    seeds = set(cfg["seed_families"])
    target_prefix = cfg["target_prefix"]
    status_names = set(cfg.get("status_count_names", ()))
    negative_terms = tuple(x.lower() for x in cfg.get("negative_name_terms", ()))

    round_modules = {
        module
        for module in paths
        if module.startswith(target_prefix)
        and is_round(module)
        and family_of(module) in seeds
    }
    parents, children = build_round_graph(imports, round_modules)

    packages: list[dict] = []
    for family in sorted(seeds):
        family_modules = {m for m in round_modules if family_of(m) == family}
        if not family_modules:
            continue
        terminal_leaves = sorted(
            m for m in family_modules if not (children.get(m, set()) & family_modules)
        )
        ancestry_by_leaf = {
            leaf: _ancestors(leaf, parents) & family_modules
            for leaf in terminal_leaves
        }
        all_ancestry = set().union(*ancestry_by_leaf.values()) if ancestry_by_leaf else set()
        decls = [_decl_dict(r) for r in decls_for_modules(conn, all_ancestry)]
        by_name: dict[str, list[dict]] = defaultdict(list)
        for decl in decls:
            by_name[decl["name"]].append(decl)

        for name in sorted(by_name):
            occurrences = sorted(
                by_name[name], key=lambda d: (d["module"], d["symbol_id"])
            )
            occurrence_modules = {d["module"] for d in occurrences}
            leaves = sorted(
                leaf
                for leaf, ancestry in ancestry_by_leaf.items()
                if ancestry & occurrence_modules
            )
            signatures = sorted({d["signature_sha256"] for d in occurrences})
            bodies = sorted({d["body_sha256"] for d in occurrences})
            neighbors = sorted(
                {
                    imported
                    for module in occurrence_modules
                    for imported in imports.get(module, ())
                    if imported in family_modules
                }
            )
            lower = name.lower()
            status_evidence = [name] if name in status_names else []
            negative_evidence = [
                term for term in negative_terms if term and term in lower
            ]
            package_id = stable_id(
                "ym-round-package",
                family,
                name,
                ",".join(signatures),
            )
            packages.append(
                {
                    "package_id": package_id,
                    "family": family,
                    "terminal_leaves": leaves,
                    "round_modules": sorted(occurrence_modules),
                    "ancestor_round_count": len(all_ancestry),
                    "declarations": occurrences,
                    "candidate_names": [name],
                    "signature_hashes": signatures,
                    "body_hashes": bodies,
                    "historical_mutation_count": max(0, len(bodies) - 1),
                    "dependency_neighbors": neighbors,
                    "status_only_evidence": status_evidence,
                    "negative_result_evidence": negative_evidence,
                    "source_locations": sorted(
                        {f"{d['file']}::{d['name']}" for d in occurrences}
                    ),
                }
            )

    return sorted(packages, key=lambda p: (p["family"], p["package_id"]))


def write_jsonl(rows: list[dict], out: Path) -> None:
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("w", encoding="utf-8") as f:
        for row in sorted(rows, key=lambda r: (r["family"], r["package_id"])):
            f.write(json.dumps(row, sort_keys=True) + "\n")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--db", default=".dashi/repository.sqlite3")
    ap.add_argument("--config", default="config/ym-round-extraction-targets.json")
    ap.add_argument("--out")
    args = ap.parse_args()

    cfg = load_targets(Path(args.config))
    conn = connect(Path(args.db))
    rows = cluster_packages(conn, cfg)
    out = Path(args.out or cfg["outputs"]["clusters"])
    write_jsonl(rows, out)
    print(json.dumps({"package_count": len(rows), "output": str(out)}, indent=2))


if __name__ == "__main__":
    main()
