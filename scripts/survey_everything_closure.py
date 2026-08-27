#!/usr/bin/env python3
"""Audit Agda import reachability from DASHI Everything entrypoints.

Repository invariant:

    first-party Agda source
      = EverythingFull-reachable
        + explicitly classified non-live unreachable
        + unexplained unreachable

All discovered first-party source is live by default.  Non-live status is an
explicit, reasoned exception in scripts/everything_nonlive.json.

This script is intentionally source-only: it does not infer typecheck success.
Join its path-level output with local .agdai evidence when available.
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
DEFAULT_NONLIVE = "scripts/everything_nonlive.json"
ALLOWED_NONLIVE_CATEGORIES = {
    "vendor",
    "generated",
    "archive",
    "superseded",
    "intentional-failing-fixture",
}


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
        if line.lstrip().startswith("--"):
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
            module = ".".join(path.relative_to(root).with_suffix("").parts)
        if module in module_to_path:
            duplicate_modules[module].extend([path, module_to_path[module]])
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


def everything_surfaces(sources: list[Path]) -> list[Path]:
    return sorted(p for p in sources if "Everything" in p.name)


def namespace_key(path: Path, root: Path, depth: int) -> str:
    rel = path.relative_to(root)
    parts = rel.parts[:-1] or rel.parts
    return "/".join(parts[:depth]) if parts else "."


def count_by_namespace(paths: list[Path], root: Path, depth: int) -> dict[str, int]:
    counts = Counter(namespace_key(path, root, depth) for path in paths)
    return dict(sorted(counts.items(), key=lambda kv: (-kv[1], kv[0])))


def load_nonlive(
    filename: str,
    root: Path,
    path_to_module: dict[Path, str],
) -> tuple[dict[str, dict[str, str]], list[str]]:
    path = (root / filename).resolve()
    if not path.exists():
        return {}, [f"non-live allowlist not found: {filename}"]
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return {}, [f"cannot read non-live allowlist {filename}: {exc}"]

    entries = payload.get("entries", [])
    if not isinstance(entries, list):
        return {}, ["non-live allowlist field 'entries' must be a list"]

    result: dict[str, dict[str, str]] = {}
    errors: list[str] = []
    seen_paths: set[str] = set()
    for i, entry in enumerate(entries):
        label = f"non-live entry #{i + 1}"
        if not isinstance(entry, dict):
            errors.append(f"{label}: must be an object")
            continue
        rel_text = entry.get("path")
        category = entry.get("category")
        reason = entry.get("reason")
        if not isinstance(rel_text, str) or not rel_text.endswith(".agda"):
            errors.append(f"{label}: path must be an exact .agda source path")
            continue
        if rel_text in seen_paths:
            errors.append(f"{label}: duplicate path {rel_text}")
            continue
        seen_paths.add(rel_text)
        if category not in ALLOWED_NONLIVE_CATEGORIES:
            errors.append(f"{label}: unsupported category {category!r}")
            continue
        if not isinstance(reason, str) or len(reason.strip()) < 8:
            errors.append(f"{label}: reason must be a concrete non-empty explanation")
            continue
        source = (root / rel_text).resolve()
        try:
            rel = source.relative_to(root)
        except ValueError:
            errors.append(f"{label}: path escapes repository root: {rel_text}")
            continue
        module = path_to_module.get(rel)
        if module is None:
            errors.append(f"{label}: source path does not exist in discovered Agda tree: {rel_text}")
            continue
        result[module] = {"path": rel_text, "category": category, "reason": reason.strip()}
    return result, errors


def write_reports(directory: Path, result: dict) -> None:
    directory.mkdir(parents=True, exist_ok=True)
    reports = {
        "unexplained_unreachable.txt": result["unexplained_unreachable"],
        "classified_nonlive_unreachable.txt": [entry["path"] for entry in result["classified_nonlive_unreachable"]],
        "classified_nonlive_reachable.txt": [entry["path"] for entry in result["classified_nonlive_reachable"]],
        "floating_everything.txt": result["floating_everything"],
    }
    for filename, lines in reports.items():
        text = "".join(f"{line}\n" for line in lines)
        (directory / filename).write_text(text, encoding="utf-8")
    (directory / "summary.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".")
    ap.add_argument("--fast", default="DASHI/EverythingFast.agda")
    ap.add_argument("--full", default="DASHI/EverythingFull.agda")
    ap.add_argument("--nonlive", default=DEFAULT_NONLIVE)
    ap.add_argument("--namespace-depth", type=int, default=2)
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--list-orphans", action="store_true", help="alias for --list-unexplained")
    ap.add_argument("--list-unexplained", action="store_true")
    ap.add_argument("--list-nonlive", action="store_true")
    ap.add_argument("--list-floating-everything", action="store_true")
    ap.add_argument("--write-reports", metavar="DIR")
    ap.add_argument("--require-live-covered", action="store_true",
                    help="exit nonzero unless every first-party source is Full-reachable or explicitly non-live")
    args = ap.parse_args()

    if args.namespace_depth < 1:
        raise SystemExit("--namespace-depth must be >= 1")

    root = Path(args.root).resolve()
    sources, module_to_path, path_to_module, graph, duplicate_modules, missing_imports = build_graph(root)
    fast_module = module_for_entry(args.fast, root, path_to_module, module_to_path)
    full_module = module_for_entry(args.full, root, path_to_module, module_to_path)

    fast = closure(fast_module, graph)
    full = closure(full_module, graph)
    all_modules = set(module_to_path)
    unreachable = all_modules - full

    nonlive, nonlive_errors = load_nonlive(args.nonlive, root, path_to_module)
    nonlive_modules = set(nonlive)
    classified_nonlive_unreachable_modules = unreachable & nonlive_modules
    classified_nonlive_reachable_modules = full & nonlive_modules
    unexplained_modules = unreachable - nonlive_modules

    # The source partition is deliberately asserted so accounting drift cannot
    # silently reappear in future audit changes.
    assert all_modules == full | unreachable
    assert not (full & unreachable)
    assert unreachable == classified_nonlive_unreachable_modules | unexplained_modules
    assert not (classified_nonlive_unreachable_modules & unexplained_modules)

    surfaces = everything_surfaces(sources)
    surface_modules = {path_to_module[p] for p in surfaces}
    floating_surface_modules = sorted(surface_modules - full)

    unexplained_paths = [module_to_path[m] for m in sorted(unexplained_modules)]
    nonlive_unreachable_entries = [nonlive[m] for m in sorted(classified_nonlive_unreachable_modules)]
    nonlive_reachable_entries = [nonlive[m] for m in sorted(classified_nonlive_reachable_modules)]

    result = {
        "source_count": len(sources),
        "fast_entry": fast_module,
        "fast_closure_count": len(fast),
        "full_entry": full_module,
        "full_closure_count": len(full),
        "full_minus_fast_count": len(full - fast),
        "unreachable_count": len(unreachable),
        "classified_nonlive_unreachable_count": len(classified_nonlive_unreachable_modules),
        "classified_nonlive_reachable_count": len(classified_nonlive_reachable_modules),
        "unexplained_unreachable_count": len(unexplained_modules),
        "everything_surface_count": len(surfaces),
        "floating_everything_surface_count": len(floating_surface_modules),
        "unexplained_by_namespace": count_by_namespace(unexplained_paths, root, args.namespace_depth),
        "unexplained_by_namespace_depth1": count_by_namespace(unexplained_paths, root, 1),
        "unexplained_by_namespace_depth2": count_by_namespace(unexplained_paths, root, 2),
        "unexplained_by_namespace_depth3": count_by_namespace(unexplained_paths, root, 3),
        "floating_everything": [str(module_to_path[m].relative_to(root)) for m in floating_surface_modules],
        "unexplained_unreachable": [str(p.relative_to(root)) for p in unexplained_paths],
        "classified_nonlive_unreachable": nonlive_unreachable_entries,
        "classified_nonlive_reachable": nonlive_reachable_entries,
        "nonlive_allowlist_errors": nonlive_errors,
        "duplicate_modules": {
            mod: sorted({str(p.relative_to(root)) for p in paths})
            for mod, paths in sorted(duplicate_modules.items())
        },
        "local_missing_import_edges": sum(len(v) for v in missing_imports.values()),
    }

    if args.write_reports:
        write_reports((root / args.write_reports).resolve(), result)

    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print(f"sources: {result['source_count']}")
        print(f"fast closure ({fast_module}): {len(fast)}")
        print(f"full closure ({full_module}): {len(full)}")
        print(f"full - fast: {len(full - fast)}")
        print(f"unreachable from full: {len(unreachable)}")
        print(f"explicit non-live unreachable: {len(classified_nonlive_unreachable_modules)}")
        print(f"unexplained unreachable (live by default): {len(unexplained_modules)}")
        print(f"explicit non-live but Full-reachable: {len(classified_nonlive_reachable_modules)}")
        print(f"Everything* surfaces: {len(surfaces)}")
        print(f"floating Everything* surfaces: {len(floating_surface_modules)}")
        print(f"non-live allowlist errors: {len(nonlive_errors)}")
        print(f"unexplained namespaces (depth={args.namespace_depth}):")
        for key, count in result["unexplained_by_namespace"].items():
            print(f"  {key}: {count}")

        if args.list_floating_everything:
            print("floating Everything* surfaces:")
            for path in result["floating_everything"]:
                print(path)

        if args.list_orphans or args.list_unexplained:
            print("unexplained unreachable sources:")
            for path in result["unexplained_unreachable"]:
                print(path)

        if args.list_nonlive:
            print("explicit non-live unreachable sources:")
            for entry in nonlive_unreachable_entries:
                print(f"{entry['path']}\t{entry['category']}\t{entry['reason']}")
            if nonlive_reachable_entries:
                print("ERROR: explicit non-live sources still reachable from EverythingFull:")
                for entry in nonlive_reachable_entries:
                    print(f"{entry['path']}\t{entry['category']}\t{entry['reason']}")

        if nonlive_errors:
            print("non-live allowlist errors:")
            for error in nonlive_errors:
                print(f"  {error}")

    if args.require_live_covered:
        violations = (
            bool(unexplained_modules)
            or bool(classified_nonlive_reachable_modules)
            or bool(nonlive_errors)
        )
        if violations:
            return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
