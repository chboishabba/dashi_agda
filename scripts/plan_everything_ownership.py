#!/usr/bin/env python3
"""Rank Everything ownership gaps by unexplained live-source payoff.

This is a migration planner, not a generator: it never edits Agda source.
It groups sources that are live-by-default but unreachable from EverythingFull,
then reports whether the namespace already has an Everything.agda owner.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from pathlib import Path

from survey_everything_closure import (
    build_graph,
    closure,
    load_nonlive,
    module_for_entry,
)


def namespace_for(path: Path, root: Path, depth: int) -> tuple[str, ...]:
    rel = path.relative_to(root)
    dirs = rel.parts[:-1]
    return tuple(dirs[:depth])


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".")
    ap.add_argument("--full", default="DASHI/EverythingFull.agda")
    ap.add_argument("--nonlive", default="scripts/everything_nonlive.json")
    ap.add_argument("--depth", type=int, default=2)
    ap.add_argument("--min-count", type=int, default=1)
    ap.add_argument("--limit", type=int, default=100)
    args = ap.parse_args()

    if args.depth < 1:
        raise SystemExit("--depth must be >= 1")

    root = Path(args.root).resolve()
    sources, module_to_path, path_to_module, graph, _, _ = build_graph(root)
    full_module = module_for_entry(args.full, root, path_to_module, module_to_path)
    full = closure(full_module, graph)
    nonlive, errors = load_nonlive(args.nonlive, root, path_to_module)
    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        return 2

    unexplained = set(module_to_path) - full - set(nonlive)
    groups: dict[tuple[str, ...], list[str]] = defaultdict(list)
    for module in unexplained:
        ns = namespace_for(module_to_path[module], root, args.depth)
        if ns:
            groups[ns].append(module)

    rows = []
    for ns, modules in groups.items():
        if len(modules) < args.min_count:
            continue
        manifest_rel = Path(*ns) / "Everything.agda"
        manifest_abs = root / manifest_rel
        manifest_exists = manifest_abs in path_to_module
        manifest_module = path_to_module.get(manifest_abs)
        manifest_reachable = bool(manifest_module and manifest_module in full)
        rows.append((len(modules), ns, manifest_rel, manifest_exists, manifest_reachable))

    rows.sort(key=lambda row: (-row[0], row[1]))
    if args.limit >= 0:
        rows = rows[: args.limit]

    print(f"unexplained live-by-default sources: {len(unexplained)}")
    print(f"ownership groups at depth {args.depth}: {len(groups)}")
    print("count\towner\tmanifest\tstatus")
    for count, ns, manifest_rel, exists, reachable in rows:
        if reachable:
            status = "owner-reachable-but-incomplete"
        elif exists:
            status = "owner-exists-but-unwired"
        else:
            status = "owner-missing"
        print(f"{count}\t{'/'.join(ns)}\t{manifest_rel}\t{status}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
