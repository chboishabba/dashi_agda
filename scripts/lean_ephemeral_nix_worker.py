#!/usr/bin/env python3
"""Ephemeral, no-checkout Lean module checker for a pinned GitHub repository.

Uses the existing DASHI flake's Lean shell (launch with
scripts/run_lean_world_nix.sh). This is an *initial* checker/closure stage,
NOT a kernel-term AST exporter, full Lake project builder or an arbitrary-code
sandbox. Only execute sources from repositories trusted for local compilation.

A module is fetched by Git blob ID, local imports staged recursively in a
temporary directory, and Lean checks it. Each source hash is retained in a
machine-readable receipt; the source workspace and generated olean disappear
on exit. Any imported external package beyond builtin Lean/Init needs an
explicit dependency-closure ID; its installation is the caller's responsibility.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import resource
import signal
import subprocess
import sys
import tempfile
import time

from lean_remote_source_inventory import (
    REPO_RE, COMMIT_RE, SHA_RE, RemoteError, request_json, source_blob,
)

IMPORT_RE = re.compile(r"^\s*import\s+(.+?)\s*(?:--.*)?$", re.MULTILINE)
MODULE_RE = re.compile(r"^[A-Za-z_][A-Za-z_0-9'.]*(?:\.[A-Za-z_][A-Za-z_0-9']*)*$")
TOOLCHAIN_RE = re.compile(r"^leanprover/lean4:(v[0-9]+\.[0-9]+\.[0-9]+(?:-[A-Za-z0-9.]+)?)$")
MAX_SOURCES = 2048
MAX_TOTAL_BYTES = 64 * 1024 * 1024


class WorkerError(RuntimeError):
    pass


def import_modules(raw: bytes) -> tuple[str, ...]:
    # Conservative dependency discovery only: Lean independently validates
    # the compiled result; supported source fragment requires ordinary imports.
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise WorkerError("Lean source is not UTF-8") from exc
    names = []
    for match in IMPORT_RE.finditer(text):
        for part in match.group(1).split():
            if not MODULE_RE.fullmatch(part):
                raise WorkerError("unsupported import syntax: " + part[:100])
            names.append(part)
    return tuple(dict.fromkeys(names))


def module_path(name: str) -> str:
    if not MODULE_RE.fullmatch(name):
        raise WorkerError("invalid Lean module path")
    result = "/".join(name.split(".")) + ".lean"
    if any(p in ("", ".", "..") for p in PurePosixPath(result).parts):
        raise WorkerError("unsafe module path")
    return result


def tree_entries(repo: str, rev: str, opener=None, token=None) -> dict[str, dict]:
    if not REPO_RE.fullmatch(repo) or not COMMIT_RE.fullmatch(rev):
        raise WorkerError("repository and immutable revision required")
    owner, name = repo.split("/")
    url = f"https://api.github.com/repos/{owner}/{name}/git/trees/{rev}?recursive=1"
    doc = request_json(url, token=token, opener=opener)
    if doc.get("truncated") is not False or not isinstance(doc.get("tree"), list):
        raise WorkerError("tree incomplete; will not fabricate import closure")
    out = {}
    for row in doc["tree"]:
        if not isinstance(row, dict) or row.get("type") != "blob":
            continue
        path, sha, size = row.get("path"), row.get("sha"), row.get("size")
        if (not isinstance(path, str) or not isinstance(sha, str)
                or not SHA_RE.fullmatch(sha) or type(size) is not int
                or size < 0):
            raise WorkerError("invalid tree entry")
        parts = PurePosixPath(path).parts
        if not parts or any(p in ("", ".", "..") for p in parts) or path.startswith("/"):
            raise WorkerError("unsafe tree path")
        out[path] = {"sha": sha, "size": size}
    return out


def pinned_version(repo: str, rev: str, tree: dict, opener=None, token=None) -> str:
    item = tree.get("lean-toolchain")
    if not item:
        raise WorkerError("pinned repository has no lean-toolchain")
    raw = source_blob(repo, item["sha"], 4096, token=token, opener=opener)
    pin = raw.decode("utf-8").strip()
    found = TOOLCHAIN_RE.fullmatch(pin)
    if not found:
        raise WorkerError("unsupported or unpinned Lean toolchain format")
    return found.group(1).removeprefix("v")


def check_version(lean: str, version: str) -> str:
    try:
        result = subprocess.run([lean, "--version"], capture_output=True,
                                text=True, timeout=15, check=False)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise WorkerError("Lean binary unavailable or version check timed out") from exc
    if result.returncode != 0:
        raise WorkerError("Lean binary version query failed")
    found = re.search(r"\bversion\s+([0-9]+\.[0-9]+\.[0-9]+(?:-[A-Za-z0-9.]+)?)", result.stdout)
    if not found or found.group(1) != version:
        raise WorkerError(f"Lean version mismatch: expected {version}, observed {result.stdout.strip()[:140]}")
    return result.stdout.strip()


def prepare_sources(repo: str, rev: str, target: str, root: Path,
                    *, opener=None, token=None, max_sources=MAX_SOURCES,
                    max_total_bytes=MAX_TOTAL_BYTES) -> tuple[list[dict], tuple[str, ...]]:
    tree = tree_entries(repo, rev, opener=opener, token=token)
    if target not in tree or not target.endswith(".lean"):
        raise WorkerError("target does not exist at pinned revision")
    queue = [target]
    observed = set()
    external = set()
    records = []
    total = 0
    while queue:
        path = queue.pop()
        if path in observed:
            continue
        if len(observed) >= max_sources:
            raise WorkerError("source closure exceeds file limit")
        item = tree[path]
        if item["size"] > max_total_bytes - total:
            raise WorkerError("source closure exceeds byte limit")
        raw = source_blob(repo, item["sha"], max_total_bytes - total,
                          token=token, opener=opener)
        total += len(raw)
        observed.add(path)
        # Do not allow source file writes to escape our temporary root.
        destination = root.joinpath(*PurePosixPath(path).parts)
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(raw)
        records.append({"path": path, "git_blob": item["sha"],
                        "sha256": hashlib.sha256(raw).hexdigest(),
                        "size": len(raw)})
        for name in import_modules(raw):
            imported_path = module_path(name)
            if imported_path in tree:
                queue.append(imported_path)
            elif not (name == "Init" or name.startswith("Init.") or
                      name == "Lean" or name.startswith("Lean.")):
                external.add(name)
    return sorted(records, key=lambda x: x["path"]), tuple(sorted(external))


def execute_lean(lean: str, root: Path, target: str, *,
                 timeout: int, memory_mib: int, lean_path: str = "") -> dict:
    if timeout < 1 or memory_mib < 128:
        raise WorkerError("invalid worker resource budget")
    output = root / ".lean-output" / "target.olean"
    output.parent.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    # Explicitly limit inherited Lean path to the documented dependency cache.
    env["LEAN_PATH"] = str(root) + (os.pathsep + lean_path if lean_path else "")
    env["LEAN_SRC_PATH"] = str(root)
    env["HOME"] = str(root / ".home")
    (root / ".home").mkdir(exist_ok=True)
    def limits():
        resource.setrlimit(resource.RLIMIT_AS, (memory_mib * 1048576, memory_mib * 1048576))
    args = [lean, f"--root={root}", "-o", str(output), str(root / target)]
    start = time.perf_counter()
    proc = subprocess.Popen(args, cwd=root, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, start_new_session=True,
                            preexec_fn=limits)
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        proc.communicate()
        raise WorkerError("Lean timed out")
    elapsed = time.perf_counter() - start
    return {"exit_code": proc.returncode, "elapsed_seconds": round(elapsed, 4),
            "stdout_tail": stdout[-4096:].decode("utf-8", "replace"),
            "stderr_tail": stderr[-4096:].decode("utf-8", "replace"),
            "olean_emitted": output.is_file()}


def run_worker(repo: str, rev: str, target: str, *, lean="lean",
               timeout=120, memory_mib=4096, dependency_closure_id="",
               lean_path="", opener=None, token=None, checker=execute_lean) -> dict:
    start = time.perf_counter()
    receipt = {"schema": "dashi-lean-ephemeral-check-v1",
               "repository": repo, "revision": rev, "target": target,
               "status": "incomplete", "declaration_ast_exported": False}
    try:
        tree = tree_entries(repo, rev, opener=opener, token=token)
        version = pinned_version(repo, rev, tree, opener=opener, token=token)
        observed_version = check_version(lean, version)
        with tempfile.TemporaryDirectory(prefix="dashi-lean-ephemeral-") as scratch:
            root = Path(scratch)
            sources, externals = prepare_sources(repo, rev, target, root,
                                                 opener=opener, token=token)
            receipt.update(toolchain=version, lean_version=observed_version,
                           source_closure=sources, external_imports=list(externals),
                           dependency_closure_id=dependency_closure_id)
            if externals and not dependency_closure_id:
                raise WorkerError("external imports require explicit pinned dependency closure ID")
            if externals and not lean_path:
                raise WorkerError("external imports require LEAN_PATH directory supplied by caller")
            result = checker(lean, root, target, timeout=timeout,
                             memory_mib=memory_mib, lean_path=lean_path)
            receipt.update(result)
            receipt["status"] = ("lean-module-checked" if
                                 result["exit_code"] == 0 and result["olean_emitted"]
                                 else "lean-check-failed")
    except (RemoteError, WorkerError, OSError, UnicodeError, ValueError) as exc:
        receipt["error"] = f"{type(exc).__name__}: {exc}"
    receipt["total_seconds"] = round(time.perf_counter() - start, 4)
    return receipt


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("repository")
    p.add_argument("revision")
    p.add_argument("target", help="repository-relative .lean file")
    p.add_argument("--lean", default=os.environ.get("LEAN_BIN", "lean"))
    p.add_argument("--timeout", type=int, default=120)
    p.add_argument("--memory-mib", type=int, default=4096)
    p.add_argument("--dependency-closure-id", default="")
    p.add_argument("--lean-path", default="")
    args = p.parse_args()
    result = run_worker(args.repository, args.revision, args.target,
                        lean=args.lean, timeout=args.timeout,
                        memory_mib=args.memory_mib,
                        dependency_closure_id=args.dependency_closure_id,
                        lean_path=args.lean_path,
                        token=os.environ.get("GITHUB_TOKEN"))
    print(json.dumps(result, sort_keys=True))
    return 0 if result["status"] == "lean-module-checked" else 2


if __name__ == "__main__":
    raise SystemExit(main())
