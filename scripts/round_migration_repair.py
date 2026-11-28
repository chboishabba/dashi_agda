#!/usr/bin/env python3
"""Generate checkpointed, mechanical repair plans for Round migration.

This tool deliberately stops before proof search.  It turns a diagnostic and a
source file into deterministic candidate edits.  Applying a plan requires the
explicit ``--apply`` flag; Agda verification is performed separately through
the repository/Colab wrapper and its receipt is then recorded by the caller.
"""

from __future__ import annotations

import argparse
import difflib
import hashlib
import json
import re
import shutil
from datetime import datetime, timezone
from pathlib import Path


def _hash(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _insert_after_module(text: str, line: str) -> str:
    lines = text.splitlines(keepends=True)
    for index, current in enumerate(lines):
        if current.startswith("module "):
            newline = "\n" if current.endswith("\n") else ""
            lines.insert(index + 1, line + newline)
            return "".join(lines)
    return line + "\n" + text


def _candidate(source: Path, before: str, after: str, rule: str, reason: str) -> dict:
    diff = "".join(difflib.unified_diff(
        before.splitlines(keepends=True), after.splitlines(keepends=True),
        fromfile=str(source), tofile=str(source),
    ))
    return {
        "rule": rule,
        "confidence": "high",
        "source": str(source),
        "before_sha256": hashlib.sha256(before.encode()).hexdigest(),
        "after_sha256": hashlib.sha256(after.encode()).hexdigest(),
        "reason": reason,
        "diff": diff,
    }


def _apply_rule(rule: str, text: str) -> str:
    if rule == "missing-builtin-list-empty":
        return _insert_after_module(text, "open import Agda.Builtin.List using ([])")
    if rule == "missing-list-concatenation":
        return _insert_after_module(text, "open import Data.List.Base using (_++_)")
    if rule == "missing-builtin-refl":
        return _insert_after_module(text, "open import Agda.Builtin.Equality using (_≡_; refl; sym)")
    if rule == "unsafe-boundary-remove-false-safe":
        return text.replace("{-# OPTIONS --safe #-}\n", "", 1)
    if rule == "malformed-ring-solver-ascription":
        return re.sub(r"\(ℚRing\.solve\s*\[\]\s*:\s*[^)]+\)", "(ℚRing.solve [])", text, count=1)
    raise ValueError(f"unknown mechanical repair rule: {rule}")


def suggest_repairs(source: Path, diagnostic: str) -> list[dict]:
    """Return non-overlapping, high-confidence mechanical edit candidates."""
    before = source.read_text(encoding="utf-8")
    candidates = []

    def add(rule: str, reason: str) -> None:
        after = _apply_rule(rule, before)
        if after != before:
            candidates.append(_candidate(source, before, after, rule, reason))

    if re.search(r"Not in scope:.*(?:\[\]|List\.\[\])", diagnostic) and "Agda.Builtin.List" not in before:
        add(
            "missing-builtin-list-empty",
            "diagnostic references the builtin empty-list constructor",
        )
    if re.search(r"Not in scope:.*(?:_\+\+_|\+\+)", diagnostic) and "Data.List.Base" not in before:
        add(
            "missing-list-concatenation",
            "diagnostic references list concatenation without the base-list import",
        )
    if re.search(r"Not in scope:.*\brefl\b", diagnostic) and "Agda.Builtin.Equality" not in before:
        add(
            "missing-builtin-refl",
            "diagnostic references refl without the builtin equality import",
        )
    if "CoInfectiveImport" in diagnostic and "{-# OPTIONS --safe #-}" in before:
        add(
            "unsafe-boundary-remove-false-safe",
            "the source declares --safe but its imported proof boundary is not safe",
        )
    if re.search(r"ℚRing\.solve\s*\[\]\s*:\s*[^\n]*equality", diagnostic):
        add(
            "malformed-ring-solver-ascription",
            "diagnostic identifies a typed ring-solver term with an invalid ascription",
        )
    return candidates


def build_repair_plan(repo_root: Path, source_path: str, diagnostic: str) -> dict:
    source = repo_root / source_path
    if not source.is_file():
        raise FileNotFoundError(source)
    candidates = suggest_repairs(source, diagnostic)
    diagnostic_class = classify_diagnostic(diagnostic)
    queue, blocking = queue_for_diagnostic(diagnostic_class)
    return {
        "schema_version": 1,
        "purpose": "dry-run mechanical repair candidates for historical Round migration",
        "scope": "historical-round-migration",
        "source": source_path,
        "source_sha256": _hash(source),
        "diagnostic_class": diagnostic_class,
        "queue": queue,
        "blocking_for_migration": blocking,
        "candidates": candidates,
        "requires_agda_receipt": True,
        "proof_search_authorized": False,
        "deletion_authorized": False,
    }


def classify_diagnostic(text: str) -> str:
    markers = (
        ("parse-error", "[ParseError]"),
        ("unsafe-import-boundary", "[CoInfectiveImport]"),
        ("unequal-terms", "Unequal terms"),
        ("unsolved-metas", "[UnsolvedMetaVariables]"),
        ("termination", "Termination checking failed"),
    )
    for name, marker in markers:
        if marker in text:
            return name
    return "unknown"


def queue_for_diagnostic(diagnostic_class: str) -> tuple[str, bool]:
    """Separate deterministic source repairs from proof obligations."""
    if diagnostic_class in {"parse-error", "unsafe-import-boundary"}:
        return "mechanical-repair", True
    return "proof-cone-external", False


def apply_plan(repo_root: Path, plan: dict, checkpoint_dir: Path, candidate_index: int) -> dict:
    source = repo_root / plan["source"]
    candidates = plan.get("candidates", [])
    if candidate_index < 0 or candidate_index >= len(candidates):
        raise ValueError("candidate index is outside the repair plan")
    candidate = candidates[candidate_index]
    current_hash = _hash(source)
    if current_hash != plan["source_sha256"] or current_hash != candidate["before_sha256"]:
        return {"status": "stale-source-skipped", "source": plan["source"], "current_sha256": current_hash}
    checkpoint_dir.mkdir(parents=True, exist_ok=True)
    checkpoint = checkpoint_dir / (source.name + "." + current_hash[:16] + ".bak")
    if not checkpoint.exists():
        shutil.copy2(source, checkpoint)
    before = source.read_text(encoding="utf-8")
    diagnostic = plan.get("diagnostic", "")
    regenerated = suggest_repairs(source, diagnostic)
    matching = next((item for item in regenerated if item["rule"] == candidate["rule"]), None)
    if not matching or matching["before_sha256"] != current_hash:
        return {"status": "candidate-revalidation-failed", "source": plan["source"]}
    after = _apply_rule(candidate["rule"], before)
    after_hash = hashlib.sha256(after.encode()).hexdigest()
    if after_hash != candidate["after_sha256"]:
        return {"status": "candidate-revalidation-failed", "source": plan["source"]}
    source.write_text(after, encoding="utf-8")
    return {
        "status": "applied",
        "source": plan["source"],
        "rule": candidate["rule"],
        "checkpoint": str(checkpoint),
        "reason": candidate["reason"],
        "before_sha256": current_hash,
        "expected_after_sha256": after_hash,
        "applied_at": datetime.now(timezone.utc).isoformat(),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", help="repository-relative Agda source path")
    parser.add_argument("--diagnostic", type=Path, required=True,
                        help="text file containing the first Agda diagnostic")
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--output", type=Path, default=Path(".dashi/round-stranded/ym-migration-repair-plan.json"))
    parser.add_argument("--apply", action="store_true",
                        help="emit a checkpointed apply decision; never deletes or invokes Agda")
    parser.add_argument("--candidate", type=int, default=0)
    parser.add_argument("--checkpoint-dir", type=Path, default=Path(".dashi/round-stranded/repair-checkpoints"))
    args = parser.parse_args()
    root = args.repo_root.resolve()
    diagnostic = args.diagnostic.read_text(encoding="utf-8")
    plan = build_repair_plan(root, args.source, diagnostic)
    plan["diagnostic"] = diagnostic
    if args.apply and plan["candidates"]:
        plan["apply_receipt"] = apply_plan(root, plan, root / args.checkpoint_dir, args.candidate)
    output = root / args.output
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(plan, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({
        "source": plan["source"],
        "diagnostic_class": plan["diagnostic_class"],
        "candidate_count": len(plan["candidates"]),
        "applied": plan.get("apply_receipt", {}).get("status", "dry-run"),
        "output": str(output),
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
