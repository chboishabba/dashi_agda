#!/usr/bin/env python3
"""Verify source-safe Karp-21 PR1445 -> PR1474 aggregate import supersets.

This checks exactly two original DASHI aggregate modules at pinned Git commits,
and makes NO mathematics/NP/Agda-kernel claims. The remaining changed docs,
referee script, transitive imports and divergent histories must be audited.
"""
from __future__ import annotations
import argparse
import json
import re
import subprocess
from pathlib import Path

OLD = "b3915126edd096cd09ce7cc1b1b195e75d9e9e87"
NEW = "fcadcb35b2d6d629952f70f2d1f46714fe77b36f"
ROOTS = (
    "DASHI/Mathematics/Complexity/Karp21Everything.agda",
    "DASHI/Mathematics/Complexity/Karp21BinaryRuntimeEverything.agda",
)
SHA40 = re.compile(r"^[0-9a-f]{40}$")
IMPORT = re.compile(r"^\s*(?:open\s+)?import\s+(DASHI(?:\.[A-Za-z_][A-Za-z_0-9]*)+)\s*$", re.M)
MODULE = re.compile(r"^\s*module\s+(DASHI(?:\.[A-Za-z_][A-Za-z_0-9]*)+)\s+where\s*$", re.M)

class Blocked(RuntimeError):
    pass

def git(repo: Path, *argv: str) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(["git", "-C", str(repo), *argv],
                          check=False, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE)

def source(repo: Path, sha: str, path: str) -> str:
    if not SHA40.fullmatch(sha) or not path in ROOTS:
        raise Blocked("unsafe commit or module request")
    if git(repo, "cat-file", "-e", f"{sha}^{{commit}}").returncode:
        raise Blocked(f"commit not fetched: {sha}")
    result = git(repo, "show", f"{sha}:{path}")
    if result.returncode:
        raise Blocked(f"source missing: {sha[:12]} {path}")
    return result.stdout.decode("utf-8")

def imported_modules(src: str, path: str) -> set[str]:
    expected = path[:-5].replace("/", ".")
    mod = MODULE.findall(src)
    if mod != [expected]:
        raise Blocked(f"wrong or repeated source module heading: {path}")
    found = IMPORT.findall(src)
    if len(found) != len(set(found)):
        raise Blocked(f"duplicate imports: {path}")
    # These roots must be import-only; no unexpectedly generated proofs may
    # be hidden behind a source-level "import superset" description.
    stripped = re.sub(r"\{-.*?-\}", "", src, flags=re.S)
    stripped = re.sub(r"--[^\n]*", "", stripped)
    rest = []
    for line in stripped.splitlines():
        line = line.strip()
        if line and not MODULE.fullmatch(line) and not IMPORT.fullmatch(line):
            rest.append(line)
    if rest:
        raise Blocked(f"aggregate now contains non-import code: {path}: {rest[:3]}")
    return set(found)

def audit(repo: Path, old: str, new: str, *, verify_targets: bool = False) -> dict:
    evidence = []
    for path in ROOTS:
        before = imported_modules(source(repo, old, path), path)
        after = imported_modules(source(repo, new, path), path)
        missing = sorted(before - after)
        added = sorted(after - before)
        if missing or not added:
            raise Blocked(f"not strict import superset: {path}; lost {missing}")
        unresolved = []
        if verify_targets:
            for module in sorted(after):
                target = module.replace(".", "/") + ".agda"
                # The new exact branch MUST own every named DASHI import.
                if git(repo, "cat-file", "-e", f"{new}:{target}").returncode:
                    unresolved.append(target)
            if unresolved:
                raise Blocked(f"unresolved new-branch imports: {path}: {unresolved}")
        evidence.append({"path":path, "old_imports":len(before),
                         "new_imports":len(after),
                         "all_old_imports_preserved":True,
                         "added_import_count":len(added),
                         "added_modules":added,
                         "verified_direct_target_presence":bool(verify_targets)})
    return {"schema":"dashi-karp-stacked-source-superset-v1",
            "source_repo":"chboishabba/dashi_agda",
            "old_commit":old, "new_commit":new,
            "roots":evidence,
            "source_import_superset_proved_by_check":True,
            "all_imports_kernel_checked":False,
            "old_1474_divergent_history_reconciled":False,
            "physical_bit_machine_polynomial_clock_proved":False,
            "SATNotInP_proved":False}

def main() -> None:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", type=Path,default=Path.cwd())
    ap.add_argument("--old", default=OLD)
    ap.add_argument("--new", default=NEW)
    ap.add_argument("--verify-targets",action="store_true")
    ap.add_argument("--json",action="store_true")
    args=ap.parse_args()
    try:
        report=audit(args.repo,args.old,args.new,
                     verify_targets=args.verify_targets)
    except (Blocked, OSError, UnicodeDecodeError) as exc:
        ap.exit(2,f"BLOCKED: {exc}\n")
    if args.json:
        print(json.dumps(report,indent=2))
    else:
        for r in report["roots"]:
            print(r["path"],r["old_imports"],"->",r["new_imports"],
                  "; preserved all; added",r["added_import_count"])
        print("SOURCE IMPORT SUPERSET ONLY; NO KERNEL/CLAY PROMOTION")

if __name__ == "__main__":
    main()
