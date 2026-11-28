#!/usr/bin/env python3
"""V01 source trust/axiom DAG report for the Yang--Mills exact-head harness.

Provenance: Docs/roadmaps/YMClayExecutionPhasesDeliverablesExactLemmas20261106.md:277

This is NOT an Agda type checker and NOT a kernel acceptance receipt. It emits a
read-only source-graph report over the local DASHI import closure: named local
postulates, unsafe pragmas/flags, declared safe modules, and external module
authorities. A transitive RealAnalysisAxioms boundary is reported, not cleared.
Usage: python3 scripts/check_ym_agda_trust_axiom_dag_20261124.py [repo-root]
"""
from __future__ import annotations

from pathlib import Path
import argparse
import json
import re
import sys

DEFAULT_ROOTS = (
    "DASHI.Unified.BalabanRGTOERegression",
    "DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact",
    "DASHI.Physics.YangMills.YMClayNativeFiniteGaugeVectorNaturalitySafeExact",
    "DASHI.Physics.YangMills.YMClaySUNConstructedPeriodicGaugeCodecExact",
    "DASHI.Physics.YangMills.YMClaySUNVariablePhysicalCutoffFamilyExact",
)

REAL_ANALYSIS_MODULE = "DASHI.Foundations.RealAnalysisAxioms"
ROADMAP_LINE = "Docs/roadmaps/YMClayExecutionPhasesDeliverablesExactLemmas20261106.md:277"

IMPORT = re.compile(r"(?m)^[ \t]*(?:open[ \t]+)?import[ \t]+([A-Za-z][\w.']+)")
POSTULATE = re.compile(r"(?m)^(?P<indent>[ \t]*)postulate(?=\s|$)(?P<rest>[^\n]*)")
OPTIONS = re.compile(r"\{\-#\s*OPTIONS\b([^\n]*?)\-\#\}")
FLAG = re.compile(r"--[A-Za-z][\w-]*")
UNSAFE_PRAGMA = re.compile(r"\{\-#\s*(TERMINATING|NON_TERMINATING)\b")
RESERVED = {
    "abstract",
    "data",
    "field",
    "infix",
    "infixl",
    "infixr",
    "instance",
    "module",
    "mutual",
    "open",
    "postulate",
    "private",
    "record",
    "syntax",
    "where",
}
EXPLICIT_UNSAFE_FLAGS = {
    "--injective-type-constructors",
    "--rewriting",
    "--type-in-type",
}


def without_comments(source: str) -> str:
    out = []
    i = 0
    depth = 0
    string = False
    while i < len(source):
        pair = source[i:i + 2]
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
        if source[i] == '"' and (i == 0 or source[i - 1] != "\\"):
            string = not string
        out.append(source[i])
        i += 1
    return "".join(out)


def declaration_names(line: str) -> list[str]:
    before, sep, _ = line.strip().partition(":")
    if not sep:
        return []
    names = []
    for token in before.split():
        if token in RESERVED or token.startswith("--"):
            continue
        if any(ch in token for ch in "(){}[];="):
            continue
        names.append(token)
    return names


def line_number(text: str, index: int) -> int:
    return text.count("\n", 0, index) + 1


def parse_postulates(clean: str) -> list[dict[str, object]]:
    lines = clean.splitlines()
    found = []
    for match in POSTULATE.finditer(clean):
        start = line_number(clean, match.start())
        base_indent = len(match.group("indent").replace("\t", " "))
        rest = match.group("rest")
        if rest.strip():
            for name in declaration_names(rest):
                found.append({"name": name, "line": start})
        offset = start
        while offset < len(lines):
            line = lines[offset]
            if not line.strip():
                offset += 1
                continue
            indent = len(line[:len(line) - len(line.lstrip())].replace("\t", " "))
            if indent <= base_indent:
                break
            for name in declaration_names(line):
                found.append({"name": name, "line": offset + 1})
            offset += 1
    return found


def parse_unsafe_flags(clean: str) -> list[dict[str, object]]:
    found = []
    for match in OPTIONS.finditer(clean):
        line = line_number(clean, match.start())
        for flag in FLAG.findall(match.group(1)):
            unsafe = (
                flag in EXPLICIT_UNSAFE_FLAGS
                or flag.startswith("--allow-")
                or flag.startswith("--no-")
            )
            if unsafe:
                found.append({"flag": flag, "line": line, "kind": "OPTIONS"})
    for match in UNSAFE_PRAGMA.finditer(clean):
        found.append({"flag": match.group(1), "line": line_number(clean, match.start()), "kind": "TERMINATION"})
    return found


def authority_label(module: str) -> str:
    if module.startswith("Agda.Primitive") or module.startswith("Agda.Builtin"):
        return "Agda built-in or primitive boundary"
    if module.startswith(("Data.", "Relation.", "Algebra.", "Function.", "Level", "Reflection.", "IO.")):
        return "Agda standard library boundary"
    if module.startswith(("Bishop", "DCHoTT", "Cubical", "Real.", "vendor.")):
        return "vendored external mathematics boundary"
    return "external module boundary"


def source_info(module: str, root: Path) -> dict[str, object] | None:
    path = root / (module.replace(".", "/") + ".agda")
    if not path.is_file():
        return None
    clean = without_comments(path.read_text(encoding="utf-8", errors="replace"))
    imports = []
    for match in IMPORT.finditer(clean):
        item = {"module": match.group(1), "line": line_number(clean, match.start())}
        if item not in imports:
            imports.append(item)
    local_imports = sorted({item["module"] for item in imports if item["module"].startswith("DASHI.")})
    external_imports = sorted({item["module"] for item in imports if not item["module"].startswith("DASHI.")})
    options = [flag for match in OPTIONS.finditer(clean) for flag in FLAG.findall(match.group(1))]
    return {
        "module": module,
        "path": str(path.relative_to(root)),
        "safe_declared": "--safe" in options,
        "options": sorted(set(options)),
        "unsafe_flags": parse_unsafe_flags(clean),
        "postulates": parse_postulates(clean),
        "imports": imports,
        "local_imports": local_imports,
        "external_imports": external_imports,
    }


def reachable_modules(root: str, edges: list[dict[str, str]]) -> list[str]:
    adjacency: dict[str, list[str]] = {}
    for edge in edges:
        adjacency.setdefault(edge["from"], []).append(edge["to"])
    seen = set()
    queue = [root]
    while queue:
        module = queue.pop()
        if module in seen:
            continue
        seen.add(module)
        queue.extend(adjacency.get(module, []))
    return sorted(seen)


def build_report(repo_root: Path, roots: list[str]) -> dict[str, object]:
    modules: dict[str, dict[str, object]] = {}
    edges: list[dict[str, str]] = []
    missing_local_imports: set[str] = set()
    queue = list(roots)
    while queue:
        module = queue.pop()
        if module in modules or module in missing_local_imports:
            continue
        info = source_info(module, repo_root)
        if info is None:
            missing_local_imports.add(module)
            continue
        modules[module] = info
        for dep in info["local_imports"]:
            edges.append({"from": module, "to": dep})
            if dep not in modules:
                queue.append(dep)

    root_reports = []
    for root in roots:
        reachable = reachable_modules(root, edges)
        postulates = [
            {"module": module, "path": modules[module]["path"], **item}
            for module in reachable if module in modules
            for item in modules[module]["postulates"]
        ]
        unsafe_flags = [
            {"module": module, "path": modules[module]["path"], **item}
            for module in reachable if module in modules
            for item in modules[module]["unsafe_flags"]
        ]
        external_authorities = [
            {
                "module": module,
                "authority": authority_label(module),
                "imported_by": sorted({
                    source for source in reachable
                    if source in modules and module in modules[source]["external_imports"]
                }),
            }
            for module in sorted({
                dep for source in reachable if source in modules
                for dep in modules[source]["external_imports"]
            })
        ]
        root_reports.append({
            "root": root,
            "reachable_local_modules": reachable,
            "safe_declared_with_transitive_postulates": [
                module for module in reachable
                if module in modules
                and modules[module]["safe_declared"]
                and postulates
            ],
            "postulate_count": len(postulates),
            "postulates": postulates,
            "unsafe_flag_count": len(unsafe_flags),
            "unsafe_flags": unsafe_flags,
            "external_authorities": external_authorities,
        })

    postulate_index = sorted({
        (module, item["line"], item["name"])
        for module, info in modules.items()
        for item in info["postulates"]
    })
    unsafe_flag_index = sorted({
        (module, item["line"], str(item["flag"]), str(item["kind"]))
        for module, info in modules.items()
        for item in info["unsafe_flags"]
    })
    real_analysis_present = REAL_ANALYSIS_MODULE in modules
    return {
        "audit": "YM_V01_TRUST_AXIOM_DAG",
        "authority": "SOURCE_GRAPH_ONLY_NOT_KERNEL_CHECK",
        "status": "V01_SOURCE_REPORT_GENERATED_NO_KERNEL_CERTIFICATION",
        "provenance": {
            "roadmap": ROADMAP_LINE,
            "scope": "read-only local DASHI import graph",
            "kernel_claim": "none",
        },
        "roots": roots,
        "modules_seen": len(modules),
        "local_import_edges": len(edges),
        "missing_local_imports": sorted(missing_local_imports),
        "modules": [
            {
                "module": module,
                "path": info["path"],
                "safe_declared": info["safe_declared"],
                "options": info["options"],
                "local_postulate_count": len(info["postulates"]),
                "local_postulates": info["postulates"],
                "unsafe_flags": info["unsafe_flags"],
                "external_imports": info["external_imports"],
            }
            for module, info in sorted(modules.items())
        ],
        "postulate_index": [
            {"module": module, "line": line, "name": name}
            for module, line, name in postulate_index
        ],
        "unsafe_flag_index": [
            {"module": module, "line": line, "flag": flag, "kind": kind}
            for module, line, flag, kind in unsafe_flag_index
        ],
        "real_analysis_boundary": {
            "present": real_analysis_present,
            "module": REAL_ANALYSIS_MODULE,
            "postulate_names": [
                item["name"] for item in modules.get(REAL_ANALYSIS_MODULE, {}).get("postulates", [])
            ],
        },
        "root_reports": root_reports,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo_root", nargs="?", help="repository root")
    parser.add_argument("--root", action="append", dest="roots", help="additional root module")
    args = parser.parse_args()
    repo_root = Path(args.repo_root).resolve() if args.repo_root else Path(__file__).resolve().parent.parent
    roots = list(DEFAULT_ROOTS)
    if args.roots:
        roots.extend(args.roots)
    print(json.dumps(build_report(repo_root, roots), indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
