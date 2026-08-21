#!/usr/bin/env python3
"""Plan the exact first-party Agda target set for repository-wide typechecking.

This is deliberately independent of the Everything import hierarchy. The
repository health question is: which maintained source files must Agda accept
before we may say "everything in the repo is typechecked"?

Known YM/NS/Balaban lanes are live but operationally heavy. The default
tractable run excludes those seed modules *and every first-party module whose
import closure reaches them*. Pass --include-heavy to include the full source
set instead.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

SOURCE_SUFFIXES = (".agda", ".lagda", ".lagda.md", ".lagda.rst", ".lagda.tex")
MODULE_RE = re.compile(r"^\s*module\s+([A-Za-z0-9_.]+)\s+where\b")
IMPORT_RE = re.compile(r"^\s*(?:open\s+)?import\s+([A-Za-z0-9_.]+)")

# Non-first-party/build infrastructure only. Keep narrow and explicit.
EXCLUDED_PARTS = {
    ".git",
    ".cache",
    "agda-toolchain",
    "cubical",
    "vendor",
    "monster",
    "_build",
}

# Operational exclusions, NOT non-live classifications.
HEAVY_PREFIXES = (
    "DASHI/Physics/YangMills/",
    "DASHI/Physics/Closure/",
    "DASHI/Papers/NavierStokes/",
)
HEAVY_NAME_FRAGMENTS = ("Balaban", "NavierStokes", "YangMills")

GENERATED_PREFIXES = ("DASHI/GeneratedEverything/",)
GENERATED_FILES = {"DASHI/EverythingGenerated.agda"}


def is_agda_source(rel: str) -> bool:
    return any(rel.endswith(suffix) for suffix in SOURCE_SUFFIXES)


def excluded_infrastructure(rel: str) -> bool:
    return any(part in EXCLUDED_PARTS for part in Path(rel).parts)


def heavy_seed(rel: str) -> bool:
    return (
        any(rel.startswith(prefix) for prefix in HEAVY_PREFIXES)
        or any(fragment in rel for fragment in HEAVY_NAME_FRAGMENTS)
    )


def generated_infrastructure(rel: str) -> bool:
    return rel in GENERATED_FILES or any(rel.startswith(p) for p in GENERATED_PREFIXES)


def load_nonlive(root: Path) -> set[str]:
    manifest = root / "scripts" / "everything_nonlive.json"
    if not manifest.exists():
        return set()
    data = json.loads(manifest.read_text())
    if isinstance(data, list):
        entries = data
    elif isinstance(data, dict):
        entries = data.get("entries", data.get("nonlive", []))
    else:
        raise ValueError(f"unsupported non-live manifest shape: {manifest}")
    result: set[str] = set()
    for entry in entries:
        if isinstance(entry, str):
            result.add(entry)
        elif isinstance(entry, dict) and isinstance(entry.get("path"), str):
            result.add(entry["path"])
    return result


def parse_module_and_imports(path: Path) -> tuple[str | None, list[str]]:
    module: str | None = None
    imports: list[str] = []
    try:
        lines = path.read_text(errors="ignore").splitlines()
    except OSError:
        return None, []
    for raw in lines:
        stripped = raw.lstrip()
        if stripped.startswith("--"):
            continue
        if module is None:
            match = MODULE_RE.match(raw)
            if match:
                module = match.group(1)
        match = IMPORT_RE.match(raw)
        if match:
            imports.append(match.group(1))
    return module, imports


def discover_sources(root: Path) -> list[str]:
    sources: list[str] = []
    for path in root.rglob("*"):
        if not path.is_file():
            continue
        rel = path.relative_to(root).as_posix()
        if is_agda_source(rel) and not excluded_infrastructure(rel):
            sources.append(rel)
    return sorted(sources)


def compute_heavy_taint(root: Path, candidates: list[str]) -> set[str]:
    module_to_path: dict[str, str] = {}
    path_imports: dict[str, list[str]] = {}

    for rel in candidates:
        module, imports = parse_module_and_imports(root / rel)
        if module:
            module_to_path[module] = rel
        path_imports[rel] = imports

    deps: dict[str, set[str]] = {}
    for rel, imports in path_imports.items():
        deps[rel] = {module_to_path[name] for name in imports if name in module_to_path}

    memo: dict[str, bool] = {}
    visiting: set[str] = set()

    def reaches_heavy(rel: str) -> bool:
        if rel in memo:
            return memo[rel]
        if heavy_seed(rel):
            memo[rel] = True
            return True
        if rel in visiting:
            return False
        visiting.add(rel)
        result = any(reaches_heavy(dep) for dep in deps.get(rel, ()))
        visiting.remove(rel)
        memo[rel] = result
        return result

    return {rel for rel in candidates if reaches_heavy(rel)}


def discover(root: Path, include_heavy: bool) -> tuple[list[str], list[str], list[str], list[str]]:
    nonlive = load_nonlive(root)
    all_sources = discover_sources(root)

    explicit_nonlive = sorted(rel for rel in all_sources if rel in nonlive)
    generated = sorted(rel for rel in all_sources if generated_infrastructure(rel))
    candidates = [
        rel
        for rel in all_sources
        if rel not in nonlive and not generated_infrastructure(rel)
    ]

    if include_heavy:
        return sorted(candidates), [], explicit_nonlive, generated

    heavy = compute_heavy_taint(root, candidates)
    selected = sorted(rel for rel in candidates if rel not in heavy)
    return selected, sorted(heavy), explicit_nonlive, generated


def write_lines(path: str | None, values: list[str]) -> None:
    if path:
        Path(path).write_text("".join(f"{v}\n" for v in values))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", default=".")
    parser.add_argument("--include-heavy", action="store_true")
    parser.add_argument("--output", help="write newline-delimited selected targets")
    parser.add_argument("--heavy-output", help="write operationally skipped heavy/tainted targets")
    parser.add_argument("--json", dest="json_output", help="write machine-readable summary")
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args()

    root = Path(args.root).resolve()
    selected, heavy, explicit_nonlive, generated = discover(root, args.include_heavy)

    if args.output:
        write_lines(args.output, selected)
    else:
        print("\n".join(selected))
    write_lines(args.heavy_output, heavy)

    summary = {
        "selected": len(selected),
        "operationally_skipped_heavy_or_tainted": len(heavy),
        "explicit_nonlive": len(explicit_nonlive),
        "generated_infrastructure": len(generated),
        "accounted_total": len(selected) + len(heavy) + len(explicit_nonlive) + len(generated),
        "include_heavy": args.include_heavy,
        "heavy_prefixes": list(HEAVY_PREFIXES),
        "heavy_name_fragments": list(HEAVY_NAME_FRAGMENTS),
    }
    if args.json_output:
        Path(args.json_output).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")

    if not args.quiet:
        print(
            "Typecheck plan: "
            f"selected={len(selected)} "
            f"heavy/tainted-skipped={len(heavy)} "
            f"explicit-nonlive={len(explicit_nonlive)} "
            f"generated-infra={len(generated)} "
            f"accounted={summary['accounted_total']}",
            file=sys.stderr,
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
