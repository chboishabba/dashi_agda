#!/usr/bin/env python3
"""Audit Agda import reachability from DASHI Everything entrypoints.

This script is intentionally source-only: it does not infer typecheck success.
Join its path-level output with scripts/survey_typechecked.py (or equivalent
local .agdai evidence) when interface caches are available.
"""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter, defaultdict, deque
from pathlib import Path

SKIP_PARTS = {".git", ".cache", "agda-toolchain", "cubical", "vendor", "monster", "_build"}
MODULE_RE = re.compile(r"^\s*module\s+([A-Za-z0-9_.]+)\s+where\b")
IMPORT_RE = re.compile(r"^\s*(?:open\s+)?import\s+([A-Za-z0-9_.]+)\b")


def skipped(path: Path) -> bool:
    return any(part in SKIP_PARTS for part in path.parts)


def discover_sources(root: Path) -> list[Path]:
    return sorted(p for p in root.rglob("*.agda") if p.is_file() and not skipped(p.relative_to(root)))


def parse_source(path: Path) -> tuple[str | None, list[str]]:
    module = None
    imports: list[str] = []
    try:
        lines = path.read_text(encoding="utf-8", errors="ignore").splitlines()
    except OSError:
        return None, imports
    for line in lines:
        stripped = line.lstrip()
        if stripped.startswith("--"):
            continue
        if module is None:
            m = MODULE_RE.match(line)
            if m:
                module = m.group(1)
        m = IMPORT_RE.match(line)
        if m:
            imports.append(m.group(1))
    return module, imports


def build_graph(root: Path):
    sources = discover_sources(root)
    module_to_path: dict[str, Path] = {}
    path_to_module: dict[Path, str] = {}
    raw_imports: dict[str, list[str]] = {}
    duplicate_modules: dict[str, list[Path]] = defaultdict(list)

    for path in sources:
        module, imports = parse_source(path)
        if not module:
            # Fall back to conventional path mapping for malformed/headerless files.
            module = ".".join(path.relative_to(root).with_suffix("").parts)
        if module in module_to_path:
            duplicate_modules[module].append(path)
            duplicate_modules[module].append(module_to_path[module])
        else:
            module_to_path[module] = path
        path_to_module[path] = module
        raw_imports[module] = imports

    graph: dict[str, set[str]] = {}
    missing_imports: dict[str, set[str]] = defaultdict(set)
    for module, imports in raw_imports.items():
        local = set()
        for imported in imports:
            if imported in module_to_path:
                local.add(imported)
            else:
                missing_imports[module].add(imported)
        graph[module] = local

    return sources, module_to_path, path_to_module, graph, duplicate_modules, missing_imports


def closure(start: str, graph: dict[str, set[str]]) -> set[str]:
    seen: set[str] = set()
    q = deque([start])
    while q:
        module = q.popleft()
        if module in seen:
            continue
        seen.add(module)
        q.extend(graph.get(module, ()))
    return seen


def module_for_entry(entry: str, root: Path, path_to_module: dict[Path, str], module_to_path: dict[str, Path]) -> str:
    candidate = (root / entry).resolve()
    try:
        rel = candidate.relative_to(root.resolve())
    except ValueError:
        rel = None
    if rel is not None and rel in path_to_module:
        return path_to_module[rel]
    if entry.endswith(".agda"):
        conventional = ".".join(Path(entry).with_suffix("").parts)
        if conventional in module_to_path:
            return conventional
    if entry in module_to_path:
        return entry
    raise SystemExit(f"entrypoint not found: {entry}")


def everything_surfaces(sources: list[Path], root: Path) -> list[Path]:
    return sorted(p for p in sources if "Everything" in p.name)


def by_top_dir(paths: list[Path], root: Path) -> dict[str, int]:
    counts = Counter()
    for path in paths:
        rel = path.relative_to(root)
        key = "/".join(rel.parts[:2]) if len(rel.parts) >= 2 else rel.parts[0]
        counts[key] += 1
    return dict(sorted(counts.items(), key=lambda kv: (-kv[1], kv[0])))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".")
    ap.add_argument("--fast", default="DASHI/EverythingFast.agda")
    ap.add_argument("--full", default="DASHI/EverythingFull.agda")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--list-orphans", action="store_true")
    ap.add_argument("--list-floating-everything", action="store_true")
    args = ap.parse_args()

    root = Path(args.root).resolve()
    sources, module_to_path, path_to_module, graph, duplicate_modules, missing_imports = build_graph(root)
    fast_module = module_for_entry(args.fast, root, path_to_module, module_to_path)
    full_module = module_for_entry(args.full, root, path_to_module, module_to_path)

    fast = closure(fast_module, graph)
    full = closure(full_module, graph)
    surfaces = everything_surfaces(sources, root)
    surface_modules = {path_to_module[p] for p in surfaces}
    floating_surface_modules = sorted(surface_modules - full)
    orphans = sorted(set(module_to_path) - full)

    result = {
        "source_count": len(sources),
        "fast_entry": fast_module,
        "fast_closure_count": len(fast),
        "full_entry": full_module,
        "full_closure_count": len(full),
        "full_minus_fast_count": len(full - fast),
        "source_orphan_count": len(orphans),
        "everything_surface_count": len(surfaces),
        "floating_everything_surface_count": len(floating_surface_modules),
        "orphan_by_top_dir": by_top_dir([module_to_path[m] for m in orphans], root),
        "floating_everything": [str(module_to_path[m].relative_to(root)) for m in floating_surface_modules],
        "orphans": [str(module_to_path[m].relative_to(root)) for m in orphans],
        "duplicate_modules": {
            mod: sorted({str(p.relative_to(root)) for p in paths})
            for mod, paths in sorted(duplicate_modules.items())
        },
        "local_missing_import_edges": sum(len(v) for v in missing_imports.values()),
    }

    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
        return 0

    print(f"sources: {result['source_count']}")
    print(f"fast closure ({fast_module}): {len(fast)}")
    print(f"full closure ({full_module}): {len(full)}")
    print(f"full - fast: {len(full - fast)}")
    print(f"source orphans from full: {len(orphans)}")
    print(f"Everything* surfaces: {len(surfaces)}")
    print(f"floating Everything* surfaces: {len(floating_surface_modules)}")
    print("orphan top dirs:")
    for key, count in result["orphan_by_top_dir"].items():
        print(f"  {key}: {count}")

    if args.list_floating_everything:
        print("floating Everything* surfaces:")
        for path in result["floating_everything"]:
            print(path)

    if args.list_orphans:
        print("orphans:")
        for path in result["orphans"]:
            print(path)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
