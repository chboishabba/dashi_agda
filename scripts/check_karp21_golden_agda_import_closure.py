#!/usr/bin/env python3
"""Fail-closed structural preflight for the Karp-21 Golden Agda import closure.

This is NOT an Agda kernel checker. It detects statically visible failures
before attempting:
    agda -i . DASHI/Mathematics/Complexity/Karp21Everything.agda

In particular Agda's --safe is coinfective: a --safe module may import only
other safe modules. Merely adding {-# OPTIONS --safe #-} to an importer does
not certify its dependencies. The current Karp-21 PR imports numerous
older unsafeguarded DASHI owners; this script reports the exact paths.

Original tool/source ownership: DASHI Agda theorem owners and the Agda
official --safe manual. This script does not change any proof term.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path

IMPORT = re.compile(r"^\s*(?:open\s+)?import\s+([A-Za-z0-9_.]+)", re.MULTILINE)
SAFE = re.compile(r"\{\-#\s*OPTIONS\b[^#]*\-\-safe\b[^#]*#\-\}")
POSTULATE = re.compile(r"^\s*postulate(?:\s|$)", re.MULTILINE)
HOLE = re.compile(r"\{!")
UNSAFE_TERMINATION = re.compile(r"\{\-#\s*(?:TERMINATING|NON_TERMINATING|NON_COVERING|NO_TERMINATION_CHECK)\b")
MODULE = re.compile(r"^\s*module\s+([A-Za-z0-9_.]+)\s+where\b", re.MULTILINE)


@dataclass(frozen=True)
class ModuleInfo:
    path: str
    name: str
    safe: bool
    postulates: bool
    holes: bool
    terminator: bool
    imports: tuple[str, ...]


def module_path(root: Path, name: str) -> Path:
    return root.joinpath(*name.split(".")).with_suffix(".agda")


def parse_module(root: Path, file: Path) -> ModuleInfo:
    text = file.read_text(encoding="utf-8")
    relative = file.relative_to(root).as_posix()
    match = MODULE.search(text)
    name = match.group(1) if match else "<missing>"
    return ModuleInfo(
        path=relative,
        name=name,
        safe=bool(SAFE.search(text)),
        postulates=bool(POSTULATE.search(text)),
        holes=bool(HOLE.search(text)),
        terminator=bool(UNSAFE_TERMINATION.search(text)),
        imports=tuple(IMPORT.findall(text)),
    )


def check(root: Path, entry: str) -> dict:
    stack: list[tuple[str, tuple[str, ...], bool]] = [(entry, (), False)]
    seen: set[tuple[str, bool]] = set()
    modules: dict[str, ModuleInfo] = {}
    issues: set[tuple[str, str, str]] = set()
    while stack:
        name, parent_chain, safe_ancestor = stack.pop()
        path = module_path(root, name)
        if not path.is_file():
            # Agda and stdlib modules are external; do not guess their safety.
            if name.startswith("DASHI."):
                issues.add(("missing-source", name, " -> ".join(parent_chain + (name,))))
            continue
        if (name, safe_ancestor) in seen:
            continue
        seen.add((name, safe_ancestor))
        info = modules.get(name)
        if info is None:
            info = parse_module(root, path)
            modules[name] = info
        chain = parent_chain + (name,)
        if info.name != name:
            issues.add(("module-path-mismatch", name, " -> ".join(chain)))
        if safe_ancestor and not info.safe:
            issues.add(("unsafe-import", name, " -> ".join(chain)))
        if info.postulates:
            issues.add(("postulate", name, " -> ".join(chain)))
        if info.holes:
            issues.add(("hole", name, " -> ".join(chain)))
        if info.terminator:
            issues.add(("unsafe-termination", name, " -> ".join(chain)))
        safe_now = safe_ancestor or info.safe
        for dependency in reversed(info.imports):
            stack.append((dependency, chain, safe_now))
    # The focused root itself must be declared Golden before its imports
    # can count as an authoritative --safe acceptance target.
    if entry in modules and not modules[entry].safe:
        issues.add(("entry-not-safe", entry, entry))
    return {
        "entry": entry,
        "reachable_repository_modules": len(modules),
        "safe_modules": sum(info.safe for info in modules.values()),
        "issues": [
            {"kind": kind, "module": module, "chain": chain}
            for kind, module, chain in sorted(issues)
        ],
        "authoritative_kernel_acceptance": False,
        "reason": "Static scan only. Agda --safe kernel acceptance must run separately.",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--entry", default="DASHI.Mathematics.Complexity.Karp21Everything")
    args = parser.parse_args()
    report = check(args.repo_root.resolve(), args.entry)
    print(json.dumps(report, indent=2, ensure_ascii=False))
    # Fail closed whenever an actual in-repository problem is detected.
    return 1 if report["issues"] else 0


if __name__ == "__main__":
    sys.exit(main())
