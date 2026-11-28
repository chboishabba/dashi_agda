#!/usr/bin/env python3
"""Fail-closed source/import preflight for the *original* Bishop CMP102 proof.

No CI, no fake kernel results. Reads actual .agda imports recursively,
tracks --safe consumers importing non-safe local producers and reports
unresolved local dependencies. Optional --typecheck runs the pinned
Agda executable if the user explicitly requests it.

Example (in a populated checkout):
 python scripts/check_ym_cmp102_original_native_imports.py \
   --repo-root . --include-root vendor/bishop --include-root vendor/stdlib
 python scripts/check_ym_cmp102_original_native_imports.py \
   --repo-root . --typecheck --agda agda
"""
from __future__ import annotations
import argparse
from collections import deque
from pathlib import Path
import re
import shutil
import subprocess
import sys

ENTRY = (
    "DASHI.Physics.YangMills."
    "YMClayCMP102Section27NativeAcceptanceExact"
)
IMPORT = re.compile(
    r"^\s*(?:(?:open\s+)?import)\s+([A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)+)",
    re.MULTILINE,
)
SAFE = re.compile(r"\{-#\s*OPTIONS\b[^#]*--safe\b[^#]*#-\}", re.MULTILINE)

def scan(repo: Path, includes: list[Path], entry: str) -> dict:
    roots = [repo] + includes
    todo = deque([entry])
    seen: set[str] = set()
    edges: list[tuple[str, str]] = []
    missing: list[str] = []
    unsafe: list[tuple[str, str]] = []
    local: dict[str, tuple[Path, bool]] = {}
    while todo:
        module = todo.popleft()
        if module in seen:
            continue
        seen.add(module)
        rel = Path(*module.split(".")).with_suffix(".agda")
        source = next((root / rel for root in roots if (root / rel).is_file()), None)
        # Agda and stdlib may expose builtin modules not shipped in repo:
        # report missing, do NOT pretend they were checked.
        if source is None:
            missing.append(module)
            continue
        body = source.read_text(encoding="utf-8")
        safe = bool(SAFE.search(body))
        local[module] = (source, safe)
        imported = IMPORT.findall(body)
        for target in imported:
            edges.append((module, target))
            todo.append(target)
    for source, target in edges:
        if source in local and target in local:
            if local[source][1] and not local[target][1]:
                unsafe.append((source, target))
    return {"visited": len(seen), "resolved": len(local),
            "missing": sorted(set(missing)), "unsafe_edges": sorted(unsafe),
            "resolved_paths": local}

def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--include-root", type=Path, action="append", default=[])
    parser.add_argument("--entry", default=ENTRY)
    parser.add_argument("--typecheck", action="store_true")
    parser.add_argument("--agda", default="agda")
    args = parser.parse_args(argv)
    root = args.repo_root.resolve()
    includes = [p.resolve() for p in args.include_root]
    result = scan(root, includes, args.entry)
    print(f"original CMP102 import graph: resolved={result['resolved']} "
          f"visited={result['visited']}")
    for source, target in result["unsafe_edges"]:
        print(f"UNSAFE-EDGE: {source} -> {target}")
    for module in result["missing"]:
        print(f"UNRESOLVED: {module}")
    if result["unsafe_edges"] or result["missing"]:
        print("PREFLIGHT NOT ACCEPTED: resolve original graph and vendor roots")
        return 1
    if not args.typecheck:
        print("PREFLIGHT ONLY: native kernel NOT RUN")
        return 0
    executable = shutil.which(args.agda)
    if executable is None:
        print("NATIVE NOT RUN: Agda executable unavailable")
        return 2
    source = result["resolved_paths"][args.entry][0]
    cmd = [executable, "-i", str(root)]
    for include in includes:
        cmd += ["-i", str(include)]
    cmd += [str(source)]
    print("Native Agda invocation:", " ".join(cmd))
    return subprocess.call(cmd)

if __name__ == "__main__":
    sys.exit(main())
