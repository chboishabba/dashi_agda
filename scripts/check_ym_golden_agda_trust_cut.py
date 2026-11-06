#!/usr/bin/env python3
"""Read-only source trust-cut audit for the Yang--Mills Golden Agda roots.

This is NOT an Agda type checker. It reports import-graph boundaries
that preclude claiming transitive 0-postulate/--safe kernel acceptance.
External stdlib imports remain marked external rather than presumed safe.
Usage: python3 scripts/check_ym_golden_agda_trust_cut.py [repo-root]
"""
from __future__ import annotations

from pathlib import Path
import json
import re
import sys

ROOTS = (
    "DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact",
    "DASHI.Physics.YangMills.YMClayNativeFiniteGaugeVectorNaturalitySafeExact",
    "DASHI.Physics.YangMills.YMClaySUNConstructedPeriodicGaugeCodecExact",
    "DASHI.Physics.YangMills.YMClaySUNVariablePhysicalCutoffFamilyExact",
    "DASHI.Unified.BalabanRGTOERegression",
)

IMPORT = re.compile(
    r"(?m)^\s*(?:open\s+)?import\s+([A-Za-z][\w.']+)"
)
POSTULATE = re.compile(r"(?m)^\s*postulate\b")
SAFE = re.compile(r"\{\-\#\s*OPTIONS\s+[^\n]*\-\-safe\b")
HOLE = re.compile(r"\{!!\}|\?")


def without_comments(source: str) -> str:
    """Strip Agda line comments and nested block comments, keep newlines."""
    out = []
    i = 0
    depth = 0
    string = False
    while i < len(source):
        pair = source[i:i+2]
        if not string and pair == "{-":
            depth += 1
            out.extend("  ")
            i += 2
            continue
        if not string and depth and pair == "-}":
            depth -= 1
            out.extend("  ")
            i += 2
            continue
        if depth:
            out.append("\n" if source[i] == "\n" else " ")
            i += 1
            continue
        if not string and pair == "--":
            while i < len(source) and source[i] != "\n":
                i += 1
            continue
        if source[i] == '"' and (i == 0 or source[i-1] != "\\"):
            string = not string
        out.append(source[i])
        i += 1
    return "".join(out)


def source_info(module: str, root: Path):
    path = root / (module.replace(".", "/") + ".agda")
    if not path.is_file():
        return None
    raw = path.read_text(encoding="utf-8")
    clean = without_comments(raw)
    return {
        "module": module,
        "path": str(path.relative_to(root)),
        "safe_declared": bool(SAFE.search(raw[:1000])),
        "postulates": len(POSTULATE.findall(clean)),
        "metas": "{!!}" in clean,
        "imports": list(dict.fromkeys(IMPORT.findall(clean))),
    }


def traverse(root: Path, name: str):
    seen = {}
    edges = []
    unavailable = set()
    queue = [name]
    while queue:
        module = queue.pop()
        if module in seen:
            continue
        info = source_info(module, root)
        if info is None:
            unavailable.add(module)
            continue
        seen[module] = info
        for dep in info["imports"]:
            if dep.startswith("DASHI."):
                edges.append((module, dep))
                if dep not in seen:
                    queue.append(dep)
    missing_safe = [
        {"module": k, "path": d["path"]}
        for k, d in seen.items() if not d["safe_declared"]
    ]
    postulates = [
        {"module": k, "path": d["path"], "count": d["postulates"]}
        for k, d in seen.items() if d["postulates"]
    ]
    return {
        "root": name,
        "modules_seen": len(seen),
        "direct_import_edges": len(edges),
        "unsafe_ancestors": missing_safe,
        "postulate_ancestors": postulates,
        "missing_local_imports": sorted(m for m in unavailable if m.startswith("DASHI.")),
        "status": "NO_SOURCE_BOUNDARY_DETECTED" if not (
            missing_safe or postulates or unavailable
        ) else "KERNEL_TRUST_OPEN",
    }


def main():
    root = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else Path(__file__).resolve().parent.parent
    results = [traverse(root, name) for name in ROOTS]
    print(json.dumps({"audit": "SOURCE_GRAPH_ONLY_NOT_KERNEL_CHECK", "roots": results}, indent=2))
    # A trust scan has no authority to certify acceptance, even if clean.
    return 0


if __name__ == "__main__":
    sys.exit(main())
