#!/usr/bin/env python3
"""Apply checked-in semantic renames without erasing historical provenance.

The registry is deliberately explicit.  This tool never guesses a replacement
for a colliding Round-numbered module; callers must add a reviewed registry
entry first.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
from pathlib import Path


TEXT_SUFFIXES = {
    ".agda", ".lean", ".md", ".json", ".py", ".sh", ".toml", ".txt"
}
SKIP_DIRS = {
    ".git", ".lake", "__pycache__", ".dashi", ".autonomous-orchestrator",
    "output", "outputs", "output-final_aristotle", "build", "target",
    "vendor", "Provenance", "Artifacts", "media", "chatgpt_browser_profile",
    "ImportedLeans",
}
SKIP_FILES = {"semantic-name-registry.json"}


def module_path(root: Path, module: str, suffix: str = ".agda") -> Path:
    return root / (module.replace(".", "/") + suffix)


def module_entry_path(
    root: Path, lean_root: Path | None, entry: dict
) -> Path:
    repository = entry.get("repo", "agda")
    if repository == "lean":
        if lean_root is None:
            raise SystemExit("Lean registry entries require --lean-root")
        return module_path(lean_root, entry["from"], ".lean")
    return module_path(root, entry["from"], ".agda")


def module_target_path(
    root: Path, lean_root: Path | None, entry: dict
) -> Path:
    repository = entry.get("repo", "agda")
    if repository == "lean":
        if lean_root is None:
            raise SystemExit("Lean registry entries require --lean-root")
        return module_path(lean_root, entry["to"], ".lean")
    return module_path(root, entry["to"], ".agda")


def load_registry(path: Path) -> tuple[list[dict], list[dict]]:
    data = json.loads(path.read_text(encoding="utf-8"))
    return data.get("module_renames", []), data.get("symbol_renames", [])


def replacement_map(modules: list[dict], symbols: list[dict]) -> dict[str, str]:
    result: dict[str, str] = {}
    for entry in modules + symbols:
        old, new = entry["from"], entry["to"]
        if old in result and result[old] != new:
            raise SystemExit(f"conflicting registry mapping for {old}")
        result[old] = new
    return result


def files_under(root: Path, needles: tuple[str, ...] = ()) -> list[Path]:
    globs = [f"*.{suffix[1:]}" for suffix in sorted(TEXT_SUFFIXES)]
    command = ["rg", "-l" if needles else "--files"]
    for pattern in globs:
        command.extend(["--glob", pattern])
    for directory in sorted(SKIP_DIRS):
        command.extend(["--glob", f"!{directory}/**"])
    if needles:
        command.append("-F")
        for needle in needles:
            command.extend(["-e", needle])
    result = subprocess.run(command, cwd=root, check=False, text=True, capture_output=True)
    if result.returncode not in (0, 1):
        raise SystemExit(result.stderr.strip() or f"file scan failed in {root}")
    return sorted(
        root / line
        for line in result.stdout.splitlines()
        if Path(line).name not in SKIP_FILES
    )


def validate(modules: list[dict], symbols: list[dict], root: Path, lean_root: Path | None) -> None:
    seen_targets: set[str] = set()
    for entry in modules:
        old, new = entry["from"], entry["to"]
        if old == new:
            raise SystemExit(f"no-op module rename: {old}")
        if new in seen_targets:
            raise SystemExit(f"duplicate module target: {new}")
        seen_targets.add(new)
        old_path = module_entry_path(root, lean_root, entry)
        new_path = module_target_path(root, lean_root, entry)
        if not old_path.exists() and not new_path.exists():
            raise SystemExit(f"missing module source and target: {old}")
        if old_path.exists() and new_path.exists():
            raise SystemExit(f"module target already exists: {new}")

    mapping = replacement_map(modules, symbols)
    old_tokens = tuple(mapping)
    roots = [root] + ([lean_root] if lean_root else [])
    stale: list[tuple[Path, str]] = []
    for search_root in roots:
        for path in files_under(search_root, old_tokens):
            text = path.read_text(encoding="utf-8", errors="replace")
            for token in old_tokens:
                if token in text:
                    stale.append((path, token))
    print(json.dumps({"registry_entries": len(mapping), "references_to_rewrite": len(stale)}, indent=2))
    for path, token in stale[:20]:
        print(f"  {path}: {token}")


def rewrite(root: Path, mapping: dict[str, str], write: bool) -> int:
    changed = 0
    for path in files_under(root, tuple(mapping)):
        old = path.read_text(encoding="utf-8", errors="replace")
        new = old
        for source, target in sorted(mapping.items(), key=lambda item: -len(item[0])):
            new = new.replace(source, target)
        if new != old:
            changed += 1
            print(f"REWRITE {path}")
            if write:
                path.write_text(new, encoding="utf-8")
    return changed


def apply_module_moves(root: Path, lean_root: Path | None, modules: list[dict]) -> None:
    for entry in modules:
        old_path = module_entry_path(root, lean_root, entry)
        new_path = module_target_path(root, lean_root, entry)
        if old_path.exists():
            new_path.parent.mkdir(parents=True, exist_ok=True)
            repository = entry.get("repo", "agda")
            git_root = lean_root if repository == "lean" else root
            subprocess.run(
                ["git", "mv", str(old_path), str(new_path)],
                check=True,
                cwd=git_root,
            )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--registry", type=Path, default=Path("config/semantic-name-registry.json"))
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument("--lean-root", type=Path)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()
    root = args.root.resolve()
    lean_root = args.lean_root.resolve() if args.lean_root else None
    modules, symbols = load_registry(args.registry)
    validate(modules, symbols, root, lean_root)
    mapping = replacement_map(modules, symbols)
    if args.check:
        print("CHECK OK")
        return
    if not args.apply:
        print("DRY RUN")
        rewrite(root, mapping, False)
        if lean_root:
            rewrite(lean_root, mapping, False)
        return
    apply_module_moves(root, lean_root, modules)
    rewrite(root, mapping, True)
    if lean_root:
        rewrite(lean_root, mapping, True)
    print("APPLY OK")


if __name__ == "__main__":
    main()
