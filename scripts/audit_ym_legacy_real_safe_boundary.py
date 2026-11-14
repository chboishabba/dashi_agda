#!/usr/bin/env python3
"""Fail-closed source audit for Agda --safe and the legacy real axiom boundary.

Checks DASHI imports against coinfectivity and reports transitive postulate
and explicitly non-safe dependencies. A source scan is NOT an Agda kernel
receipt, and external stdlib/vendor imports are not certified by this script.
"""
from __future__ import annotations
import argparse
import json
import re
from pathlib import Path

IMPORT = re.compile(r"^\s*(?:open\s+)?import\s+(DASHI(?:\.[A-Za-z0-9_]+)+)", re.M)
SAFE = re.compile(r"\{-#\s*OPTIONS\s+[^#]*--safe(?:\s|#|-|$)")
POSTULATE = re.compile(r"^\s*postulate(?:\s|$)", re.M)
ROOTS = [
    "DASHI/Physics/YangMills/BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact.agda",
    "DASHI/Physics/YangMills/BalabanHeatDoobFromSameDensityExpectationRound108Exact.agda",
    "DASHI/Physics/YangMills/BalabanBC2CompactGroupSameDensityRound119Exact.agda",
    "DASHI/Physics/YangMills/BalabanCMP109116ConstructiveScalarCoreExact.agda",
    "DASHI/Physics/YangMills/YangMillsStressOSCommonSemigroupDerivativeExact.agda",
]

def path_for(module: str) -> str:
    return module.replace(".", "/") + ".agda"

def audit(root: Path, roots: list[str]) -> dict:
    inspected: dict[str, dict] = {}
    def inspect(path: str):
        if path in inspected:
            return
        local = root / path
        if not local.is_file():
            inspected[path] = {"missing": True}
            return
        code = local.read_text(encoding="utf-8")
        imports = sorted({path_for(name) for name in IMPORT.findall(code)})
        inspected[path] = {
            "safe": bool(SAFE.search(code)),
            "local_postulate": bool(POSTULATE.search(code)),
            "imports": imports,
        }
        for dep in imports:
            inspect(dep)

    for root_name in roots:
        inspect(root_name)

    direct = []
    for path, value in inspected.items():
        if value.get("missing"):
            continue
        if value["safe"]:
            for dep in value["imports"]:
                meta = inspected[dep]
                if meta.get("missing") or not meta.get("safe"):
                    direct.append({"importer": path, "imported": dep,
                        "reason": "missing" if meta.get("missing") else "non-safe dependency"})
            if value["local_postulate"]:
                direct.append({"importer": path, "imported": path,
                    "reason": "local postulate"})
    transitive = []
    for root_name in roots:
        found = set()
        todo = [root_name]
        while todo:
            p = todo.pop()
            if p in found:
                continue
            found.add(p)
            todo.extend(inspected.get(p, {}).get("imports", []))
        violations = sorted(p for p in found
            if inspected.get(p, {}).get("missing")
            or inspected[p].get("local_postulate")
            or not inspected[p].get("safe"))
        transitive.append({
            "root": root_name,
            "safe_source_closure": len(violations) == 0,
            "violations": violations,
        })
    return {
        "checked_roots": roots,
        "visited_dashi_modules": len(inspected),
        "source_co_infectivity_violations": direct,
        "root_trust_closures": transitive,
        "external_imports_kernel_verified": False,
        "agda_kernel_accepted": False,
        "legacy_real_axioms_eliminated_globally": False,
    }

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--repo", type=Path, default=Path.cwd())
    p.add_argument("--root", action="append", dest="roots")
    p.add_argument("--json", action="store_true")
    p.add_argument("--strict", action="store_true")
    args = p.parse_args()
    result = audit(args.repo, args.roots or ROOTS)
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        for x in result["root_trust_closures"]:
            print(("SAFE_SOURCE_CLOSURE" if x["safe_source_closure"] else "UNSAFE_OR_UNVERIFIED"),
                x["root"], "violations:", len(x["violations"]))
        print("Direct safe-import violations:", len(result["source_co_infectivity_violations"]))
        print("NO AGDA KERNEL RECEIPT")
    if args.strict and (result["source_co_infectivity_violations"]
        or any(not x["safe_source_closure"] for x in result["root_trust_closures"])):
        p.exit(2, "BLOCKED: unresolved legacy-real / --safe trust boundary\n")

if __name__ == "__main__":
    main()
