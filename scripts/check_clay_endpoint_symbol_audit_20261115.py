#!/usr/bin/env python3
"""Fail-closed rollup-only exact-symbol and phase-ledger preflight.

Authoritative input:
  Docs/roadmaps/ClaySixFrontierABCExactGates20261114.json
  .six_endpoint_exact_symbol_audit_20261115.symbol_index

Run from Agda Clay #1499 checkout:
  python3 scripts/check_clay_endpoint_symbol_audit_20261115.py
  python3 scripts/check_clay_endpoint_symbol_audit_20261115.py --lean-root ../dashi_lean4

This is a SOURCE-STRUCTURE audit, not Agda/Lean kernel acceptance.
It never changes files or silently promotes terminal gates.
"""
from __future__ import annotations
import argparse
from collections import Counter
from pathlib import Path
import json
import re
import subprocess
import sys

AUDIT = "six_endpoint_exact_symbol_audit_20261115"
LEDGER = "Docs/roadmaps/ClaySixFrontierABCExactGates20261114.json"
ROOT = Path(__file__).resolve().parents[1]
SIMPLE = re.compile(r"^[A-Za-z_][A-Za-z_0-9.]*$")
STATUS = {
    "SOURCE_TERM_UNCHECKED", "SOURCE_CANDIDATE_UNCHECKED",
    "CONDITIONAL_RECORD", "CONDITIONAL_COMPILER", "EXPLICIT_OPEN_FLAG",
    "OPEN_ENUM_CONSTRUCTOR", "TARGET_NAME_ONLY", "TARGET_TYPE_UNINHABITED",
    "COST_MODEL_COVERAGE_CONSTRUCTED", "KNOWN_NEGATIVE_CONTROL",
    "REFUTED_UNIVERSAL_AUX", "CONDITIONAL_EQUIVALENCE", "SOURCE_MODULE_REUSED",
}

def tracked_source(root: Path) -> list[Path]:
    try:
        result = subprocess.run(
            ["git", "-C", str(root), "ls-files", "-z", "--", "*.agda", "*.lean"],
            capture_output=True, check=True,
        )
    except (OSError, subprocess.CalledProcessError) as exc:
        raise RuntimeError(f"Need original checked-out Git tree: {exc}") from exc
    return [root / p.decode() for p in result.stdout.split(b"\0") if p]

def git_blob_sha(root: Path, filename: str) -> str:
    """Hash exact original file bytes using Git's content-addressed format."""
    path = root / filename
    result = subprocess.run(
        ["git", "-C", str(root), "hash-object", "--", str(path)],
        capture_output=True, text=True, check=True,
    )
    return result.stdout.strip()

def declaration(body: str, name: str) -> bool:
    target = name.split(".")[-1]
    # Agda declarations/record fields and Lean theorem/def/structure names.
    expr = re.compile(
        rf"^\s*(?:(?:theorem|lemma|def|noncomputable\s+def|record|data|"
        rf"structure|abbrev|instance)\s+)?{re.escape(target)}\s*(?::|=|where\b)",
        re.M,
    )
    return bool(expr.search(body))

def main() -> int:
    arg = argparse.ArgumentParser()
    arg.add_argument("--lean-root", type=Path, help="Optional exact native Lean #108 checkout")
    arg.add_argument("--strict", action="store_true",
                     help="Fail if source declarations are missing or target-only names gained bodies")
    opts = arg.parse_args()
    ledger = ROOT / LEDGER
    if not ledger.is_file():
        print(f"BLOCKED: missing canonical {ledger}", file=sys.stderr)
        return 2
    data = json.loads(ledger.read_text())
    audit = data[AUDIT]
    index = audit["symbol_index"]
    if len(index) < 100 or len(audit["gates"]) != 15:
        print("BLOCKED: canonical ledger truncated", file=sys.stderr)
        return 2
    roots = {"agda": ROOT}
    if opts.lean_root:
        roots["lean"] = opts.lean_root.resolve()
    files = {k: tracked_source(v) for k, v in roots.items()}
    cache: dict[Path, str] = {}
    def body(path: Path) -> str:
        if path not in cache:
            cache[path] = path.read_text(encoding="utf-8", errors="replace")
        return cache[path]
    counts = Counter()
    problems = []
    # Audit the actual content-addressed source receipts, not filenames alone.
    evidence = audit.get("p0_source_evidence", {})
    original = evidence.get("observed", {})
    lean_receipts = evidence.get("lean_sources", {})
    if len(original) != 47 or len(lean_receipts) != 3:
        problems.append("P0_RECEIPT_TRUNCATED: expected 47 Agda and 3 Lean owners")
    # The gate manifest must reflect the original P0 source acceptance and
    # the explicitly user-authorized C1 Python/SymPy mathematical acceptance;
    # C1 must not masquerade as native Agda kernel acceptance.
    manifest = audit.get("gates", [])
    completed = [g["id"] for g in manifest if g.get("closed", False)]
    active = [g["id"] for g in manifest if not g.get("closed", False)]
    if (len(manifest) != 15
            or audit.get("active_gate_count") != 13
            or audit.get("active_gate_ids") != active
            or audit.get("completed_gate_ids") != ["P0", "C1"]
            or completed != ["P0", "C1"]):
        problems.append("PHASE_GATE_COUNT_MISMATCH: expected P0+C1 (Python math), 13 active")
    c1 = next((g for g in manifest if g["id"] == "C1"), None)
    if (c1 is None
            or c1.get("status") != "CLOSED_MATHEMATICAL_PYTHON_SYMPY"
            or c1.get("native_agda_theorem_inhabited") is not False
            or c1.get("native_kernel_proof_receipt") is not False
            or c1.get("physical_R408_time_packet_constructed") is not False
            or not (ROOT / "scripts/check_clay_c1_r71_r74_sympy_bridge_20261115.py").is_file()):
        problems.append("C1_PYTHON_CLOSURE_PROTOCOL_OR_NATIVE_DEBT_MISSING")
    for owner, receipt in original.items():
        if (ROOT / owner).is_file():
            actual = git_blob_sha(ROOT, owner)
            if actual != receipt["blob"]:
                problems.append(f"P0_AGDA_OWNER_CHANGED {owner}: {actual} != {receipt['blob']}")
        else:
            problems.append(f"P0_AGDA_OWNER_MISSING {owner}")
    if "lean" in roots:
        for owner, receipt in lean_receipts.items():
            if (roots["lean"] / owner).is_file():
                actual = git_blob_sha(roots["lean"], owner)
                if actual != receipt["blob"]:
                    problems.append(f"P0_LEAN_OWNER_CHANGED {owner}: {actual} != {receipt['blob']}")
            else:
                problems.append(f"P0_LEAN_OWNER_MISSING {owner}")
    # Every historical donor exact blob identity has an independently fetched
    # SHA in the ledger; ensure the local Clay copy retains that exact content.
    p0 = next((g for g in audit["gates"] if g["id"] == "P0"), None)
    if p0 is None or not p0.get("closed"):
        problems.append("P0_NOT_CLOSED_OR_MISSING")
    else:
        for pair in p0["acceptance_evidence"]["donor_blob_matches"]:
            filename = pair["path"]
            if (ROOT / filename).is_file():
                actual = git_blob_sha(ROOT, filename)
                if actual != pair["donor_blob"]:
                    problems.append(f"P0_DONOR_BLOB_CHANGED {filename}")
            else:
                problems.append(f"P0_DONOR_BLOB_MISSING {filename}")
    for entry in index:
        name = entry["term"]
        kind = entry["classification"]
        lane = entry["lane"]
        owner = entry["owner"]
        root = roots.get(entry["repo"])
        counts[f"{lane}:{kind}"] += 1
        if kind not in STATUS:
            problems.append(f"UNKNOWN_CLASS {lane}: {name} ({kind})")
            continue
        if root is None:
            counts["LEAN_CHECKOUT_NOT_PROVIDED"] += 1
            continue
        path = root / owner
        if not path.is_file():
            problems.append(f"OWNER_MISSING {lane}: {owner} for {name}")
            continue
        if kind == "SOURCE_MODULE_REUSED":
            continue  # Module/source file verified above, not an identically named binder.
        if not SIMPLE.fullmatch(name):
            continue  # Explicit natural-language and compound gate labels.
        leaf = name.split(".")[-1]
        actual = declaration(body(path), name)
        # A target may be superseded by an existing declaration in some other
        # original source owner; do not pretend default-branch search is enough.
        if kind == "TARGET_NAME_ONLY":
            matches = [str(p.relative_to(root)) for p in files[entry["repo"]]
                       if declaration(body(p), name)]
            if matches:
                problems.append(
                    f"RECLASSIFY_TARGET {lane}: {name} now declared in {matches[:4]}"
                )
            continue
        if kind in {
            "SOURCE_TERM_UNCHECKED", "SOURCE_CANDIDATE_UNCHECKED",
            "COST_MODEL_COVERAGE_CONSTRUCTED", "EXPLICIT_OPEN_FLAG",
        } and not actual:
            # It can be a sourced import rather than a local binder; inspect,
            # don't automatically call it disproved.
            problems.append(f"VERIFY_DECLARATION {lane}: {name} in {owner}")
        if kind == "EXPLICIT_OPEN_FLAG" and actual:
            flagged = re.search(rf"^\s*{re.escape(leaf)}\s*=\s*false\b", body(path), re.M)
            if not flagged:
                problems.append(f"FLAG_CHANGED {lane}: {name} no longer '= false'")
    print(json.dumps({
        "schema": "six-endpoint-source-audit-run-v1",
        "repo": str(ROOT), "symbol_entries": len(index),
        "phase_gates": len(audit["gates"]), "classification_counts": counts,
        "problems": problems,
        "claim": "SOURCE_STRUCTURE_ONLY_NOT_KERNEL_CERTIFICATION",
    }, indent=2, sort_keys=True, default=dict))
    if problems and opts.strict:
        return 1
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
