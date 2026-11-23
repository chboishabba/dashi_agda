#!/usr/bin/env python3
"""
audit_proof_states.py - Audit proof states, LeafState declarations, and formalization levels
across DASHI Agda and Lean4 files.
"""

import os
import re
import sys
from collections import defaultdict
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

# Patterns for state types and constructors
DATA_STATE_PAT = re.compile(r'^\s*data\s+([A-Za-z0-9_]*State[A-Za-z0-9_]*|[A-Za-z0-9_]*Status[A-Za-z0-9_]*|[A-Za-z0-9_]*Phase[A-Za-z0-9_]*)\s*:', re.MULTILINE)
CONSTRUCTOR_LINE_PAT = re.compile(r'^\s+([A-Za-z0-9_ ]+)\s*:\s*([A-Za-z0-9_]+)', re.MULTILINE)
MAPPING_PAT = re.compile(r'^\s*([a-z][A-Za-z0-9_]*State[A-Za-z0-9_]*|[a-z][A-Za-z0-9_]*Status[A-Za-z0-9_]*)\s*:\s*([A-Za-z0-9_]+)\s*→\s*([A-Za-z0-9_]+)', re.MULTILINE)
STATUS_COMMENT_PAT = re.compile(r'--\s*(?:STATUS|FORMALIZATION|PROOF STATE|PAYMENT|PHASE):\s*(.*)', re.IGNORECASE)

def scan_agda_proof_states():
    results = {
        "state_types": {},
        "mapping_functions": {},
        "summary_counts": defaultdict(int),
        "files_with_open_states": [],
        "files_with_closed_states": [],
        "round_leaf_states": {}
    }

    dashi_dir = REPO_ROOT / "DASHI"
    for agda_file in dashi_dir.rglob("*.agda"):
        try:
            content = agda_file.read_text(encoding="utf-8", errors="replace")
        except Exception:
            continue

        rel_path = agda_file.relative_to(REPO_ROOT)

        # Check for state definitions
        for match in DATA_STATE_PAT.finditer(content):
            type_name = match.group(1)
            # Find the constructors in the block
            start = match.end()
            block = content[start:start+400]
            constructors = []
            for c_match in CONSTRUCTOR_LINE_PAT.finditer(block):
                c_names = c_match.group(1).split()
                if c_match.group(2) == type_name:
                    constructors.extend(c_names)
            
            results["state_types"][f"{rel_path}:{type_name}"] = constructors
            for c in constructors:
                results["summary_counts"][c] += 1
                if "open" in c.lower():
                    results["files_with_open_states"].append(str(rel_path))
                if "closed" in c.lower():
                    results["files_with_closed_states"].append(str(rel_path))

            # Round files
            round_match = re.search(r'Round(\d+)', agda_file.name)
            if round_match:
                round_num = int(round_match.group(1))
                results["round_leaf_states"][round_num] = {
                    "file": str(rel_path),
                    "type": type_name,
                    "constructors": constructors
                }

        # Check for state mappings (e.g. leafState leafX = openState)
        for match in MAPPING_PAT.finditer(content):
            fn_name = match.group(1)
            in_type = match.group(2)
            out_type = match.group(3)
            results["mapping_functions"][f"{rel_path}:{fn_name}"] = (in_type, out_type)

    return results

def main():
    print("=" * 70)
    print("DASHI FORMALIZATION LEVEL & LEAFSTATE AUDIT")
    print("=" * 70)

    res = scan_agda_proof_states()

    print(f"\nTotal State Types Discovered: {len(res['state_types'])}")
    print(f"Total State Transition Mappings: {len(res['mapping_functions'])}")
    print(f"Total Round Modules with LeafState: {len(res['round_leaf_states'])}")

    print("\n--- Top State Constructors Across the Codebase ---")
    for c, count in sorted(res["summary_counts"].items(), key=lambda x: -x[1])[:25]:
        print(f"  {c:<30}: {count} occurrences")

    print("\n--- Sample LeafState Definitions Across Domains ---")
    sample_types = list(res["state_types"].items())[:15]
    for name, ctors in sample_types:
        print(f"  {name}: {' | '.join(ctors)}")

    print(f"\nFiles with 'open' state leaves: {len(set(res['files_with_open_states']))}")
    print(f"Files with 'closed' state leaves: {len(set(res['files_with_closed_states']))}")

    if res["round_leaf_states"]:
        print("\n--- Balaban / Yang-Mills / NS Round Trajectory (Sample) ---")
        for r in sorted(res["round_leaf_states"].keys())[:10]:
            info = res["round_leaf_states"][r]
            print(f"  Round {r:<4} ({Path(info['file']).name}): {info['type']} -> {' | '.join(info['constructors'])}")

if __name__ == "__main__":
    main()
