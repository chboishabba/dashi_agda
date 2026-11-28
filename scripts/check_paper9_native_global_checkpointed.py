#!/usr/bin/env python3
"""Local staged Paper 9 kernel replay. Never turns a diagnostic into proof.
Run in the pinned Agda environment from a clean committed checkout.
Each successful stage is recorded atomically; a failed/timeout stage is retried.
The strict --safe lane is separate from the diagnostic lane.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
MOON = "DASHI/Moonshine/"
PREFIX = "CM163BishopHecke41"
STAGES = tuple(MOON + PREFIX + name + ".agda" for name in (
    "UnramifiedResidualExact",
    "DyadicFourierProjectionExact",
    "UniformSeriesContinuityExact",
    "CuspContractionExact",
    "DyadicCircleBoundsExact",
    "FourierCoefficientBoundExact",
    "QuantitativeRigidityExact",
    "LocatedOrbitReductionExact",
    "ActualOrbitCoverExact",
    "GlobalMatrixRigidityExact",
    "OriginalRayClosureExact",
    "NativeFiniteAcceptanceExact",
    "AllIntegerNodesAcceptanceExact",
    "OriginalGlobalAcceptanceExact",
))
TERMINAL = STAGES[-1]


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


def atomic_json(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", dir=path.parent, delete=False) as tmp:
        temp = Path(tmp.name)
        json.dump(obj, tmp, sort_keys=True, indent=2)
        tmp.write("\n")
        tmp.flush()
        os.fsync(tmp.fileno())
    os.replace(temp, path)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def code_only(source):
    # Preserve pragmas while removing nested ordinary comments and line comments.
    out, i, depth = [], 0, 0
    while i < len(source):
        if depth:
            if source.startswith("{-", i):
                depth += 1
                i += 2
            elif source.startswith("-}", i):
                depth -= 1
                i += 2
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif source.startswith("{-#", i):
            j = source.find("#-}", i)
            if j < 0:
                raise ValueError("unterminated pragma")
            out.append(source[i:j+3])
            i = j + 3
        elif source.startswith("{-", i):
            depth = 1
            i += 2
        elif source.startswith("--", i):
            j = source.find("\n", i)
            i = len(source) if j < 0 else j
        elif source[i] == '"':
            # Strings cannot introduce imports or authority syntax.
            i += 1
            while i < len(source) and source[i] != '"':
                i += 2 if source[i] == "\\" else 1
            i += 1
            out.append(" ")
        else:
            out.append(source[i])
            i += 1
    if depth:
        raise ValueError("unterminated comment")
    return "".join(out)


IMPORT = re.compile(r"\b(?:open\s+)?import\s+([\w.\-]+)", re.UNICODE)
RISK = re.compile(
    r"(?m)^\s*postulate\b|\{!|\bprimTrustMe\b|"
    r"\{-#\s*(?:TERMINATING|NON_TERMINATING|NO_TERMINATION_CHECK|"
    r"NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|REWRITE)\b|"
    r"--(?:allow-unsolved-metas|allow-incomplete-matches|"
    r"no-termination-check|no-positivity-check|type-in-type|"
    r"no-universe-check|rewriting)\b"
)


def source_audit(extra_roots):
    roots = [ROOT, ROOT/"vendor/bishop", ROOT/"DCHoTT-Agda",
             ROOT/"cubical", *map(Path, extra_roots)]
    seen, unresolved, risks = {}, set(), []
    pending = [ROOT/TERMINAL]
    while pending:
        path = pending.pop().resolve()
        if str(path) in seen:
            continue
        src = code_only(path.read_text(encoding="utf-8"))
        seen[str(path)] = digest(path)
        for match in RISK.finditer(src):
            risks.append({"path": str(path), "line": src.count("\n", 0, match.start())+1,
                          "token": match.group(0).strip()})
        for module in IMPORT.findall(src):
            rel = Path(*module.split(".")).with_suffix(".agda")
            options = [root/rel for root in roots]
            found = next((p for p in options if p.is_file()), None)
            if found:
                pending.append(found)
            else:
                unresolved.add(module)
    # This is a lexical preflight, not a full elaborated dependency analysis.
    return {"sources": seen, "unresolved_imports": sorted(unresolved),
            "authority_candidates": risks,
            "scope": "reachable lexical imports in supplied roots; kernel is authoritative"}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--checkpoint", type=Path, required=True)
    ap.add_argument("--budget", type=float, default=80)
    ap.add_argument("--agda", default="agda")
    ap.add_argument("--include", action="append", default=[])
    ap.add_argument("--audit-only", action="store_true")
    ap.add_argument("--diagnostic-unsafe", action="store_true",
                    help="ordinary typecheck only, never strict acceptance")
    args = ap.parse_args()
    if not 0 < args.budget <= 85:
        ap.error("budget must be in (0,85], use external timeout 90s")
    start = time.monotonic()
    audit = source_audit(args.include)
    audit_path = args.checkpoint.with_suffix(".audit.json")
    atomic_json(audit_path, audit)
    print("SOURCE_AUDIT", len(audit["sources"]), "files;",
          len(audit["unresolved_imports"]), "unresolved imports;",
          len(audit["authority_candidates"]), "authority candidates", flush=True)
    if args.audit_only:
        print("AUDIT_ONLY: no kernel acceptance", flush=True)
        return 0
    executable = shutil.which(args.agda)
    if not executable:
        print("BLOCKED: Agda executable absent; no acceptance", flush=True)
        return 2
    if git("status", "--porcelain", "--untracked-files=no"):
        raise RuntimeError("commit tracked changes before acceptance")
    submodules = git("submodule", "status", "--recursive")
    if any(line[:1] in "-+U" for line in submodules.splitlines()):
        raise RuntimeError("submodule checkout missing or differs from pin")
    version = subprocess.check_output([executable, "--version"], text=True, timeout=10).strip()
    flags = ["-l", "dashi-agda"] + ([] if args.diagnostic_unsafe else ["--safe"])
    for path in args.include:
        flags.extend(["-i", str(Path(path).resolve())])
    header = {"schema": 1, "head": git("rev-parse", "HEAD"),
              "submodules": submodules, "agda": version,
              "executable": str(Path(executable).resolve()),
              "executable_sha256": digest(Path(executable).resolve()),
              "flags": flags, "source_audit": audit,
              "lane": "diagnostic" if args.diagnostic_unsafe else "strict-safe"}
    state = json.loads(args.checkpoint.read_text()) if args.checkpoint.exists() else {
        "header": header, "passed": {}, "attempts": []}
    if state.get("header") != header:
        raise RuntimeError("checkpoint source/environment mismatch; choose a new checkpoint")
    if set(state["passed"]) - set(STAGES):
        raise RuntimeError("unknown checkpoint stage")
    logs = args.checkpoint.with_suffix(".logs")
    logs.mkdir(parents=True, exist_ok=True)
    for i, stage in enumerate(STAGES):
        if stage in state["passed"]:
            receipt = state["passed"][stage]
            log = logs/receipt["log"]
            if not log.is_file() or digest(log) != receipt["sha256"]:
                raise RuntimeError("missing or changed stage receipt")
            continue
        remaining = args.budget - (time.monotonic() - start)
        if remaining <= 0:
            print("BUDGET: earlier receipts retained", flush=True)
            break
        log = logs/f"{i:02d}-{len(state['attempts']):04d}.log"
        argv = [executable, *flags, stage]
        print("RUN", *argv, flush=True)
        with log.open("wb") as out:
            proc = subprocess.Popen(argv, cwd=ROOT, stdout=out,
                                    stderr=subprocess.STDOUT, start_new_session=True)
            try:
                rc = proc.wait(timeout=remaining)
                status = "PASS" if rc == 0 else "FAIL"
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
                rc, status = None, "TIMEOUT"
        receipt = {"stage": stage, "status": status, "returncode": rc,
                   "log": log.name, "sha256": digest(log)}
        state["attempts"].append(receipt)
        if status == "PASS":
            state["passed"][stage] = receipt
        atomic_json(args.checkpoint, state)
        print(status, stage, "log", log, flush=True)
        if status != "PASS":
            return 124 if status == "TIMEOUT" else 1
    complete = set(state["passed"]) == set(STAGES)
    # A receipt is execution evidence, never an Agda proof term.
    if complete and not args.diagnostic_unsafe:
        print("STRICT_KERNEL_REPLAY_COMPLETE: review actual source/authority and GMP attachment")
    elif complete:
        print("DIAGNOSTIC_COMPLETE: not strict acceptance")
    else:
        print("CHECKPOINT", len(state["passed"]), "/", len(STAGES))
    return 0 if complete else 3


if __name__ == "__main__":
    raise SystemExit(main())
