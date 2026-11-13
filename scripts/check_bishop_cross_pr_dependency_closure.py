#!/usr/bin/env python3
"""Fail-closed Agda DASHI import closure across TWO PINNED Git commits.

This is a local source-transplant planner, NOT a typechecker, proof certificate,
analytic theorem, or authorization to merge. No network, CI or Docker needed.
It stages missing original donor bytes only outside the checked-out source.

  python3 scripts/check_bishop_cross_pr_dependency_closure.py \
    --baseline 28d85aa529155352a025de9e12853ecad1e4214e \
    --donor c19bb2c7c3b01d493975b31c868ffa9da46eb0b9 \
    --root DASHI/Analysis/BishopComplexExpFactEqualsNativeExpExact.agda \
    --stage-dir /tmp/dashi-bishop-1408-1478 --json
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

SHA = re.compile(r"^[0-9a-f]{40}$")
PATH = re.compile(r"^DASHI/(?:[A-Za-z0-9_]+/)*[A-Za-z0-9_]+\.agda$")
IMPORT = re.compile(
    r"^\s*(?:open\s+)?import\s+(DASHI(?:\.[A-Za-z0-9_]+)+)",
    re.MULTILINE,
)


class Blocked(RuntimeError):
    pass


def git(repo, *args):
    return subprocess.run(
        ["git", "-C", str(repo), *args], capture_output=True, check=False
    )


def source(repo, commit, path):
    if not SHA.fullmatch(commit) or not PATH.fullmatch(path):
        raise Blocked("non-pinned commit or unsafe source path")
    result = git(repo, "show", f"{commit}:{path}")
    if result.returncode:
        return None
    try:
        result.stdout.decode("utf-8")
    except UnicodeDecodeError as e:
        raise Blocked(f"non-UTF8 source: {path}") from e
    return result.stdout


def closure(repo, baseline, donor, roots):
    if not roots or any(not PATH.fullmatch(path) for path in roots):
        raise Blocked("invalid Agda roots")
    for rev in (baseline, donor):
        if not SHA.fullmatch(rev) or git(repo, "cat-file", "-e", f"{rev}^{{commit}}").returncode:
            raise Blocked(f"missing exact local commit: {rev}")
    pending = list(roots)
    modules = {}
    while pending:
        path = pending.pop()
        if path in modules:
            continue
        old = source(repo, baseline, path)
        new = source(repo, donor, path)
        if old is None and new is None:
            modules[path] = {"status": "UNRESOLVED"}
            continue
        content = old if old is not None else new
        status = "BASELINE" if old is not None else "DONOR_TRANSFER"
        imports = sorted(
            name.replace(".", "/") + ".agda"
            for name in set(IMPORT.findall(content.decode("utf-8")))
        )
        modules[path] = {
            "status": status,
            "sha256": hashlib.sha256(content).hexdigest(),
            "imports": imports,
            "donor_differs": old is not None and new is not None and old != new,
        }
        pending.extend(dep for dep in imports if dep not in modules)
    counts = {k: sum(v["status"] == k for v in modules.values()) for k in
              ("BASELINE", "DONOR_TRANSFER", "UNRESOLVED")}
    return {
        "baseline": baseline, "donor": donor, "roots": roots,
        "counts": counts,
        "dashi_imports_closed": counts["UNRESOLVED"] == 0,
        "kernel_accepted": False,
        "source_semantics_checked": False,
        "external_imports_checked": False,
        "modules": dict(sorted(modules.items())),
    }


def stage(repo, donor, result, directory):
    if not result["dashi_imports_closed"]:
        raise Blocked("missing modules in BOTH commits, refusing partial stage")
    if directory.exists() and any(directory.iterdir()):
        raise Blocked("stage directory nonempty, refusing overwrite")
    for path, meta in result["modules"].items():
        if meta["status"] != "DONOR_TRANSFER":
            continue
        data = source(repo, donor, path)
        if data is None or hashlib.sha256(data).hexdigest() != meta["sha256"]:
            raise Blocked(f"donor source changed while staging: {path}")
        output = directory / path
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(data)
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "DASHI_AGDA_TRANSFER_MANIFEST.json").write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", type=Path, default=Path.cwd())
    p.add_argument("--baseline", required=True)
    p.add_argument("--donor", required=True)
    p.add_argument("--root", action="append", required=True)
    p.add_argument("--stage-dir", type=Path)
    p.add_argument("--json", action="store_true")
    args = p.parse_args()
    try:
        report = closure(args.repo, args.baseline, args.donor, args.root)
        if args.stage_dir:
            stage(args.repo, args.donor, report, args.stage_dir)
        if args.json:
            print(json.dumps(report, indent=2, ensure_ascii=False))
        else:
            print("Bishop cross-PR D A S H I source closure:", report["counts"])
            for path, info in report["modules"].items():
                if info["status"] != "BASELINE":
                    print(info["status"], path)
            print("NO KERNEL RECEIPT; Agda 2.9 typechecking remains mandatory.")
        if not report["dashi_imports_closed"]:
            raise Blocked("DASHI modules missing in both exact source commits")
    except Blocked as error:
        p.exit(2, f"BLOCKED: {error}\n")


if __name__ == "__main__":
    main()
