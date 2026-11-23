#!/usr/bin/env python3
"""
Scan and inventory all LeafState definitions and open leaf obligations in DASHI Agda.
Identifies:
1. Leaf enum types (e.g. StoneVonNeumannProofLeaf, PreferredRowCLeaf259, RH8894Leaf)
2. LeafState types (leafOpen, leafClosed, leafBlocked, etc.)
3. Mapping functions (leafState, preferred*LeafState, etc.)
4. Exact open leaves and their dependencies
"""

import os
import re
from pathlib import Path

REPO_ROOT = Path("/home/c/Documents/code/dashi_agda")
DASHI_DIR = REPO_ROOT / "DASHI"

LEAF_STATE_PATTERN = re.compile(
    r"data\s+([A-Za-z0-9_]*LeafState[A-Za-z0-9_]*|FinalLeafState|LeafState)\s*:\s*Set[^\n]*where\s*\n([^;]+?)(?=\n\n|\n[a-z]|\n--|\Z)",
    re.MULTILINE
)

LEAF_ASSIGN_PATTERN = re.compile(
    r"^([a-zA-Z0-9_]+LeafState[a-zA-Z0-9_]*|leafState|finalLeafState|preferred[A-Za-z0-9_]*LeafState[A-Za-z0-9_]*)\s+([a-zA-Z0-9_]+)\s*=\s*([a-zA-Z0-9_.]+)",
    re.MULTILINE
)

OPEN_KEYWORDS = {"leafOpen", "openState", "waiting", "unpaid", "live", "optional"}
CLOSED_KEYWORDS = {"leafClosed", "closed", "paid", "owned", "sourceMerged"}
BLOCKED_KEYWORDS = {"leafBlocked", "blocked", "pruned", "downstream", "diagnostic"}

def scan():
    results = []
    for agda_file in sorted(DASHI_DIR.rglob("*.agda")):
        try:
            content = agda_file.read_text(encoding="utf-8", errors="replace")
        except Exception:
            continue
            
        assignments = LEAF_ASSIGN_PATTERN.findall(content)
        if not assignments:
            continue
            
        rel_path = agda_file.relative_to(REPO_ROOT)
        file_leaves = {"open": [], "closed": [], "blocked": []}
        
        for fn_name, leaf_name, state in assignments:
            clean_state = state.split(".")[-1]
            if clean_state in OPEN_KEYWORDS:
                file_leaves["open"].append((leaf_name, clean_state))
            elif clean_state in CLOSED_KEYWORDS:
                file_leaves["closed"].append((leaf_name, clean_state))
            elif clean_state in BLOCKED_KEYWORDS:
                file_leaves["blocked"].append((leaf_name, clean_state))
            else:
                # check if substring matches
                if any(k in clean_state for k in ("Open", "open")):
                    file_leaves["open"].append((leaf_name, clean_state))
                elif any(k in clean_state for k in ("Closed", "closed")):
                    file_leaves["closed"].append((leaf_name, clean_state))
                else:
                    file_leaves["blocked"].append((leaf_name, clean_state))
                    
        results.append({
            "file": str(rel_path),
            "open_count": len(file_leaves["open"]),
            "closed_count": len(file_leaves["closed"]),
            "blocked_count": len(file_leaves["blocked"]),
            "open_leaves": file_leaves["open"],
            "closed_leaves": file_leaves["closed"],
            "blocked_leaves": file_leaves["blocked"]
        })
        
    print(f"Scanned {len(results)} files with formal LeafState mappings.")
    print("=" * 80)
    
    total_open = sum(r["open_count"] for r in results)
    total_closed = sum(r["closed_count"] for r in results)
    total_blocked = sum(r["blocked_count"] for r in results)
    print(f"TOTAL: {total_open} Open, {total_closed} Closed, {total_blocked} Blocked/Pruned across {len(results)} frontier modules.\n")
    
    # Sort files by open_count descending
    results.sort(key=lambda r: r["open_count"], reverse=True)
    for r in results:
        if r["open_count"] > 0:
            print(f"File: {r['file']}")
            print(f"  Open ({r['open_count']}): {', '.join(name for name, _ in r['open_leaves'])}")
            if r['closed_count'] > 0:
                print(f"  Closed ({r['closed_count']}): {', '.join(name for name, _ in r['closed_leaves'][:5])}...")
            if r['blocked_count'] > 0:
                print(f"  Blocked ({r['blocked_count']}): {', '.join(name for name, _ in r['blocked_leaves'][:5])}...")
            print()

if __name__ == "__main__":
    scan()
