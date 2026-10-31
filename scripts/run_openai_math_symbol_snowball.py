#!/usr/bin/env python3
"""Batch queries over the EXISTING dashi-repo semantic index and local Lean checkout.

This is NOT a second symbol index and NEVER creates a separate SQLite DB.
Agda semantic similarity/history belongs to tools/agda_preflight/dashi-repo.
Plain-text rg is an optional cross-prover and history fallback, not evidence
of formal theorem equality. Discover-before-prove and no ESD edits.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys

TERM_FILE = (Path(__file__).resolve().parents[1] / "docs/superpowers/plans"
             / "2026-10-31-local-symbol-snowball-terms.json")
EXTENSIONS = ("*.agda", "*.lean", "*.py")


def parse_groups(path: Path, selected: set[str], max_terms: int):
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("schema") != "dashi-symbol-snowball-v1":
        raise ValueError("unexpected or stale term pack schema")
    if not isinstance(max_terms, int) or max_terms < 1:
        raise ValueError("--max-terms must be a positive integer")
    groups = sorted(payload["groups"], key=lambda g: (g["priority"], g["lane"]))
    if selected:
        missing = selected - {g["lane"] for g in groups}
        if missing:
            raise ValueError(f"unknown group(s): {', '.join(sorted(missing))}")
        groups = [g for g in groups if g["lane"] in selected]
    count = 0
    seen = set()
    for group in groups:
        for term in group["search_terms"]:
            if term in seen:
                continue
            seen.add(term)
            yield group, term
            count += 1
            if count >= max_terms:
                return


def run_command(args: list[str], max_lines: int):
    """Bound the display, not the search; never execute command via shell."""
    proc = subprocess.run(args, capture_output=True, text=True, check=False,
                          encoding="utf-8", errors="replace")
    if proc.returncode not in (0, 1):
        return [], f"exit={proc.returncode} stderr={proc.stderr.strip()[:240]}"
    lines = [s for s in proc.stdout.splitlines() if s.strip()]
    return lines[:max_lines], None


def rg_command(root: Path, term: str, limit: int):
    return ["rg", "--no-heading", "--line-number", "--fixed-strings",
            "--color", "never", "--max-columns", "260",
            "--max-count", str(limit), "--glob", "*.agda",
            "--glob", "*.lean", "--glob", "*.py", "--glob", "!*ESD*",
            "--glob", "!*digital_esd*", "--", term, str(root)]


def semantic_command(root: Path, term: str, limit: int):
    return ["dashi-repo", "symbol", term, "--root", str(root),
            "--limit", str(limit)]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--terms-file", type=Path, default=TERM_FILE)
    parser.add_argument("--agda-root", type=Path, default=Path.cwd())
    parser.add_argument("--lean-root", type=Path,
                        help="separate local dashi_lean4 checkout, if present")
    parser.add_argument("--group", action="append", default=[],
                        help="P0, P1, P2, P3, P4, P5, R00, ..., or R07; repeat")
    parser.add_argument("--max-terms", type=int, default=36,
                        help="top N priority-ordered unique queries; default 36")
    parser.add_argument("--max-lines", type=int, default=8,
                        help="max displayed matches per command; default 8")
    parser.add_argument("--mode", choices=["plan", "native", "grep", "both"],
                        default="plan",
                        help="plan is non-mutating; native uses canonical dashi-repo DB")
    parser.add_argument("--discover", action="store_true",
                        help="also ask dashi-repo for fail-closed discovery receipt")
    parser.add_argument("--related", action="store_true",
                        help="also query exact known owner symbol with native related")
    parser.add_argument("--out", type=Path,
                        help="write a TSV/command plan (optional; no cache DB)")
    args = parser.parse_args(argv)
    if args.max_lines < 1:
        parser.error("--max-lines must be positive")

    agda = args.agda_root.resolve()
    if not agda.is_dir():
        parser.error(f"Agda root does not exist: {agda}")
    lean = args.lean_root.resolve() if args.lean_root else None
    if lean is not None and not lean.is_dir():
        parser.error(f"Lean root does not exist: {lean}")
    use_native = args.mode in ("native", "both")
    use_grep = args.mode in ("grep", "both")
    if use_native and shutil.which("dashi-repo") is None:
        parser.error("dashi-repo missing: pip install -e './tools/agda_preflight[mcp,test]'")
    if use_grep and shutil.which("rg") is None:
        parser.error("rg missing: install ripgrep or use --mode native")

    output = [
        "# This is a SEARCH RECEIPT, never a theorem-acceptance receipt.",
        "# Native Agda matcher: dashi-repo; optional Lean/ripgrep hits are keyword-only.",
        "# Search hits must be inspected for same quantified carrier, hypotheses and conclusion.",
        "lane\tquery\tbackend\tresult_or_command",
    ]
    selected = set(args.group)
    try:
        jobs = list(parse_groups(args.terms_file, selected, args.max_terms))
    except (ValueError, KeyError, json.JSONDecodeError) as exc:
        parser.error(f"term pack: {exc}")
    groups_seen = {}
    for group, term in jobs:
        lane = group["lane"]
        groups_seen.setdefault(lane, group)
        tasks = [( "native", semantic_command(agda, term, args.max_lines))]
        if args.discover:
            tasks.append(("discovery", ["dashi-repo", "discover", term,
                                         "--root", str(agda),
                                         "--limit", str(args.max_lines)]))
        for root in filter(None, (agda, lean)):
            tasks.append(("rg", rg_command(root, term, args.max_lines)))
        for backend, command in tasks:
            if args.mode == "plan":
                output.append(f"{lane}\t{term}\t{backend}\t{shlex.join(command)}")
                continue
            if backend in ("native", "discovery") and not use_native:
                continue
            if backend == "rg" and not use_grep:
                continue
            lines, error = run_command(command, args.max_lines)
            if error:
                output.append(f"{lane}\t{term}\t{backend}\tERROR {error}")
            else:
                for item in lines:
                    safe = item.replace("\t", " ").replace("\n", " ")
                    output.append(f"{lane}\t{term}\t{backend}\t{safe}")
                if not lines:
                    output.append(f"{lane}\t{term}\t{backend}\tNO_MATCH"
                                  " (NOT an absence certificate)")

    if args.related:
        for lane, group in groups_seen.items():
            for symbol in group.get("related_symbols", ()):
                command = ["dashi-repo", "related", symbol,
                           "--root", str(agda), "--limit", str(args.max_lines)]
                if args.mode == "plan":
                    output.append(f"{lane}\t{symbol}\trelated\t{shlex.join(command)}")
                elif use_native:
                    lines, error = run_command(command, args.max_lines)
                    output.extend(f"{lane}\t{symbol}\trelated\t{z}"
                                  for z in (lines or [error or "NO_MATCH"]))
    report = "\n".join(output) + "\n"
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(report, encoding="utf-8")
        print(f"Saved {len(output)-4} search/command rows to {args.out}")
    else:
        sys.stdout.write(report)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
