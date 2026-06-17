#!/usr/bin/env python3
"""Estimate surface area metrics for Agda module dependencies.

This script performs static analysis only over local `.agda` files:
- counts discovered modules and import statements
- identifies direct importers of queried modules
- computes reverse transitive importer cones
- emits a compact risk bucket from impact size

No non-stdlib dependencies are used.
"""

from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict, deque
from pathlib import Path
from typing import Iterable, List, Sequence

MODULE_DECL_RE = re.compile(r"^\s*module\s+([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\s+where\b", re.MULTILINE)
IMPORT_RE = re.compile(
    r"^\s*(?:open\s+)?import\s+([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\b",
    re.MULTILINE,
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path.cwd(),
        help="Repository root to scan (default: current working directory)",
    )
    parser.add_argument(
        "--module",
        action="append",
        default=[],
        help="Target module name (can be repeated)",
    )
    parser.add_argument(
        "--path",
        action="append",
        default=[],
        help="Target module path (file path or module-style prefix) (can be repeated)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Emit JSON output",
    )
    parser.add_argument(
        "--top-importers",
        nargs="?",
        type=int,
        const=10,
        default=None,
        metavar="N",
        help="Show top N modules by direct-importer count (default 10 when flag is given)",
    )
    return parser.parse_args()


def strip_comments(source: str) -> str:
    """Remove Agda line and nested block comments from a source string."""
    out: List[str] = []
    i = 0
    depth = 0
    n = len(source)
    while i < n:
        ch = source[i]
        nxt = source[i + 1] if i + 1 < n else ""

        if ch == "-" and nxt == "-" and depth == 0:
            while i < n and source[i] != "\n":
                i += 1
            continue

        if ch == "{" and nxt == "-":
            depth += 1
            i += 2
            continue

        if ch == "-" and nxt == "}" and depth > 0:
            depth -= 1
            i += 2
            continue

        if depth == 0:
            out.append(ch)
        i += 1

    return "".join(out)


def to_module_name(path: Path, repo_root: Path) -> str:
    rel = path.relative_to(repo_root) if path.is_relative_to(repo_root) else path
    parts = rel.with_suffix("").parts
    return ".".join(parts)


def scan_agda_files(repo_root: Path) -> tuple[list[Path], int]:
    files = sorted(p for p in repo_root.rglob("*.agda") if p.is_file())
    return files, len(files)


def build_dependency_graph(
    files: Sequence[Path],
    repo_root: Path,
) -> tuple[dict[str, set[str]], dict[str, set[str]], dict[Path, str], list[tuple[str, int]]]:
    imports_for: dict[str, set[str]] = {}
    reverse_importers: dict[str, set[str]] = defaultdict(set)
    file_to_module: dict[Path, str] = {}
    per_file_counts: list[tuple[str, int]] = []

    for path in files:
        text = path.read_text(encoding="utf-8")
        clean = strip_comments(text)

        module_match = MODULE_DECL_RE.search(clean)
        module_name = module_match.group(1) if module_match else None
        if module_name is None:
            # Best effort when module declaration is missing or parser-unfriendly.
            module_name = to_module_name(path, repo_root)

        file_to_module[path.resolve()] = module_name

        module_imports: set[str] = set()
        for import_match in IMPORT_RE.finditer(clean):
            imported = import_match.group(1)
            module_imports.add(imported)
            reverse_importers[imported].add(module_name)

        imports_for[module_name] = module_imports
        per_file_counts.append((module_name, len(module_imports)))

    return imports_for, reverse_importers, file_to_module, per_file_counts


def deduce_target_modules(
    args: argparse.Namespace,
    repo_root: Path,
    all_modules: set[str],
    file_to_module: dict[Path, str],
) -> tuple[list[str], list[str]]:
    targets: set[str] = set(args.module)
    missing: list[str] = []

    for raw in args.path:
        path_like = Path(raw)
        abs_path = path_like if path_like.is_absolute() else repo_root / path_like

        if abs_path.exists():
            if abs_path.is_file() and abs_path.suffix == ".agda":
                module_name = file_to_module.get(abs_path)
                if module_name is None:
                    module_name = to_module_name(abs_path, repo_root)
                targets.add(module_name)
                continue

            if abs_path.is_dir():
                prefix = to_module_name(abs_path, repo_root)
                matched = {
                    m
                    for m in all_modules
                    if m == prefix or m.startswith(prefix + ".")
                }
                if matched:
                    targets.update(matched)
                else:
                    missing.append(str(raw))
                continue

        candidate = raw.replace("/", ".")
        if candidate.endswith(".agda"):
            candidate = candidate[:-5]

        if candidate in all_modules:
            targets.add(candidate)
            continue

        # Prefix/suffix module matching for partial path/module references.
        prefix_hits = {m for m in all_modules if m.startswith(candidate)}
        suffix_hits = {m for m in all_modules if m.endswith(candidate)} if "." in candidate else set()
        hits = prefix_hits or suffix_hits
        if hits:
            targets.update(hits)
        else:
            missing.append(raw)

    resolved = sorted(targets)
    return resolved, missing


def reverse_transitive_cone(
    targets: Iterable[str],
    reverse_importers: dict[str, set[str]],
) -> tuple[set[str], list[str]]:
    frontier = deque(targets)
    seen: set[str] = set()
    ordered: list[str] = []
    while frontier:
        current = frontier.popleft()
        for importer in sorted(reverse_importers.get(current, ())):
            if importer in seen:
                continue
            seen.add(importer)
            ordered.append(importer)
            frontier.append(importer)
    return seen, ordered


def risk_bucket(direct_count: int, cone_size: int, all_modules: int, total_imports: int) -> tuple[str, int]:
    score = (direct_count * 3) + (2 * cone_size)
    score += 1 if total_imports > all_modules * 6 else 0

    if score <= 12:
        return "low", score
    if score <= 36:
        return "medium", score
    return "high", score


def top_importer_modules(
    reverse_importers: dict[str, set[str]],
    n: int,
) -> list[tuple[str, int]]:
    counts = [(module, len(importers)) for module, importers in reverse_importers.items()]
    counts.sort(key=lambda item: (-item[1], item[0]))
    return counts[:n]


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    files, file_count = scan_agda_files(repo_root)

    imports_for, reverse_importers, file_to_module, per_file_counts = build_dependency_graph(
        files,
        repo_root,
    )

    all_modules = set(imports_for.keys())

    targets, missing = deduce_target_modules(
        args,
        repo_root,
        all_modules,
        file_to_module,
    )

    if not targets:
        if args.module or args.path:
            print(
                "No target modules resolved from provided --module/--path. Could not match: "
                + ", ".join(dict.fromkeys(args.module + args.path))
            )
            if missing:
                print("Unmatched targets: " + ", ".join(missing))
            return 2
        print("No query target provided. Use --module or --path.")
        return 2

    total_modules = len(all_modules)
    total_imports = sum(count for _, count in per_file_counts)

    direct_importers: dict[str, list[str]] = {}
    for module in targets:
        importers = sorted(reverse_importers.get(module, set()))
        direct_importers[module] = importers

    union_direct_importers = sorted({m for ims in direct_importers.values() for m in ims})
    reverse_cone, reverse_order = reverse_transitive_cone(targets, reverse_importers)

    score_bucket, score = risk_bucket(len(union_direct_importers), len(reverse_cone), total_modules, total_imports)

    top_importers: list[tuple[str, int]] | None = None
    if args.top_importers:
        top_importers = top_importer_modules(reverse_importers, args.top_importers)

    if args.json:
        payload = {
            "repo_root": str(repo_root),
            "scanned_agda_files": file_count,
            "module_count": total_modules,
            "import_statement_count": total_imports,
            "query": {
                "module_flags": args.module,
                "path_flags": args.path,
                "targets": targets,
            },
            "direct_importers": {
                "count": len(union_direct_importers),
                "modules": union_direct_importers,
                "by_target": direct_importers,
            },
            "reverse_transitive_cone": {
                "size": len(reverse_cone),
                "modules": sorted(reverse_cone),
                "order_bfs": reverse_order,
            },
            "risk": {
                "bucket": score_bucket,
                "score": score,
                "heuristic": {
                    "direct_importers_weight": 3,
                    "reverse_cone_weight": 2,
                },
            },
            "unresolved_query_targets": missing,
        }

        if top_importers is not None:
            payload["top_importers"] = [
                {"module": module, "direct_importer_count": count}
                for module, count in top_importers
            ]

        print(json.dumps(payload, indent=2))
        return 0

    print(f"Scanned .agda files: {file_count}")
    print(f"Modules: {total_modules}")
    print(f"Imports: {total_imports}")
    print(f"Target modules: {', '.join(targets)}")
    print(f"Direct importers: {len(union_direct_importers)}")
    print(f"  {', '.join(union_direct_importers) if union_direct_importers else '(none)'}")
    print(f"Reverse transitive cone size: {len(reverse_cone)}")
    if reverse_cone:
        print(f"  {', '.join(sorted(reverse_cone))}")
    print(f"Risk bucket: {score_bucket} (score {score})")

    if top_importers is not None:
        print(f"Top {len(top_importers)} direct-importer modules:")
        for module, count in top_importers:
            print(f"  {module}: {count}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
