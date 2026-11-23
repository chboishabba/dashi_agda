#!/usr/bin/env python3
"""
cross_repo_proof_inventory.py - Comprehensive cross-repo inventory of open proof obligations,
LeafState tracks, and formalization tiers across DASHI Agda and Lean 4.
"""

import os
import re
import sys
from collections import defaultdict
from pathlib import Path

AGDA_ROOT = Path("/home/c/Documents/code/dashi_agda")
LEAN_ROOT = Path("/home/c/Documents/code/dashi_lean4")

TIER_OPEN = {"leafOpen", "openState", "waiting", "unpaid", "open"}
TIER_CONDITIONAL = {"partialPaid", "candidate", "sourceMerged", "sourceBacked", "conditional"}
TIER_CLOSED = {"leafClosed", "closed", "paid"}
TIER_BLOCKED = {"leafBlocked", "blocked", "pruned", "refuted"}

def scan_agda():
    obligations = []
    dashi_dir = AGDA_ROOT / "DASHI"
    for path in dashi_dir.rglob("*.agda"):
        try:
            content = path.read_text(encoding="utf-8", errors="replace")
        except Exception:
            continue
        rel = path.relative_to(AGDA_ROOT)

        for line_num, line in enumerate(content.splitlines(), start=1):
            line_str = line.strip()
            # Look for tier keywords as constructors, return types, or status comments
            for kw in TIER_OPEN | TIER_CONDITIONAL | TIER_CLOSED | TIER_BLOCKED:
                if re.search(r'\b' + re.escape(kw) + r'\b', line_str):
                    tier = "OPEN" if kw in TIER_OPEN else (
                        "CONDITIONAL" if kw in TIER_CONDITIONAL else (
                            "CLOSED" if kw in TIER_CLOSED else "BLOCKED"
                        )
                    )
                    obligations.append({
                        "repo": "agda",
                        "file": str(rel),
                        "line": line_num,
                        "keyword": kw,
                        "tier": tier,
                        "text": line_str[:120]
                    })
                    break
    return obligations

def scan_lean():
    obligations = []
    for path in LEAN_ROOT.rglob("*.lean"):
        if ".lake" in path.parts or ".git" in path.parts:
            continue
        try:
            content = path.read_text(encoding="utf-8", errors="replace")
        except Exception:
            continue
        rel = path.relative_to(LEAN_ROOT)

        for line_num, line in enumerate(content.splitlines(), start=1):
            line_str = line.strip()
            # Lean sorry, admit, candidate, conditional, openState
            if re.search(r'\b(sorry|admit)\b', line_str) and not line_str.startswith("--"):
                obligations.append({
                    "repo": "lean4",
                    "file": str(rel),
                    "line": line_num,
                    "keyword": "sorry/admit",
                    "tier": "OPEN",
                    "text": line_str[:120]
                })
            else:
                for kw in TIER_OPEN | TIER_CONDITIONAL | TIER_CLOSED | TIER_BLOCKED:
                    if re.search(r'\b' + re.escape(kw) + r'\b', line_str):
                        tier = "OPEN" if kw in TIER_OPEN else (
                            "CONDITIONAL" if kw in TIER_CONDITIONAL else (
                                "CLOSED" if kw in TIER_CLOSED else "BLOCKED"
                            )
                        )
                        obligations.append({
                            "repo": "lean4",
                            "file": str(rel),
                            "line": line_num,
                            "keyword": kw,
                            "tier": tier,
                            "text": line_str[:120]
                        })
                        break
    return obligations

def main():
    print("Scanning Agda obligations...")
    agda_obs = scan_agda()
    print("Scanning Lean obligations...")
    lean_obs = scan_lean()

    agda_by_tier = defaultdict(list)
    for o in agda_obs:
        agda_by_tier[o["tier"]].append(o)

    lean_by_tier = defaultdict(list)
    for o in lean_obs:
        lean_by_tier[o["tier"]].append(o)

    print("\n=== AGDA PROOF INVENTORY BY TIER ===")
    for tier in ["OPEN", "CONDITIONAL", "CLOSED", "BLOCKED"]:
        print(f"  {tier:12}: {len(agda_by_tier[tier])} occurrences")

    print("\n=== LEAN 4 PROOF INVENTORY BY TIER ===")
    for tier in ["OPEN", "CONDITIONAL", "CLOSED", "BLOCKED"]:
        print(f"  {tier:12}: {len(lean_by_tier[tier])} occurrences")

    # Group open by domain
    print("\n=== TOP AGDA MODULES WITH OPEN OBLIGATIONS ===")
    agda_open_files = defaultdict(int)
    for o in agda_by_tier["OPEN"]:
        agda_open_files[o["file"]] += 1
    for f, count in sorted(agda_open_files.items(), key=lambda x: -x[1])[:20]:
        print(f"  {count:3} open: {f}")

    print("\n=== TOP LEAN 4 MODULES WITH OPEN OBLIGATIONS ===")
    lean_open_files = defaultdict(int)
    for o in lean_by_tier["OPEN"]:
        lean_open_files[o["file"]] += 1
    for f, count in sorted(lean_open_files.items(), key=lambda x: -x[1])[:20]:
        print(f"  {count:3} open: {f}")

if __name__ == "__main__":
    main()
