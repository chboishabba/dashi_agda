#!/usr/bin/env python3
"""Powered and derived quotient word search for Monster 3B -> ATLAS generators.

Searches powered words in the authentic Dietrich-Lee-Pisani-Popiel (2026)
Monster normalizer generators (g3b, h3b) on E/Z(E) =~ F3^12.
Reuses the authentic manifest from mmgroup extraction, verifies exact ATLAS
semipresentation relations, and tests the 144-variable GF(3) intertwiner system
and symplectic similitude form transport.
"""

import argparse
import json
import sys
import time
from pathlib import Path

# Add scripts directory to path
SCRIPTS_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPTS_DIR.parent
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))

from monster3b_atlas_mmgroup_bounded_word_search import enumerate_words
from monster3b_atlas_mmgroup_cross_source_intertwiner_gate import (
    atlas, check_pair, eye, form_monster, form_source, monster_matrix,
    mul, neg, powm, rank, source_relations, transpose
)

def freeze(m):
    return bytes(x for row in m for x in row)

def format_powered_word(word_tokens: list[str], power: int) -> dict:
    return {
        "base_word": word_tokens,
        "power": power,
        "display": f"({' * '.join(word_tokens)})^{power}" if len(word_tokens) > 1 else f"{word_tokens[0]}^{power}"
    }

def run_powered_search(
    manifest_path: Path,
    root: Path,
    depth: int = 4,
    max_base_states: int = 3000,
    max_power: int = 120,
    max_pairs: int = 10000,
    time_limit: float = 90.0,
) -> dict:
    start_time = time.time()
    
    if not manifest_path.is_file():
        raise FileNotFoundError(f"Missing manifest file: {manifest_path}")

    manifest = json.loads(manifest_path.read_text())
    lifts = manifest.get("normalizer_lifts", [])
    if len(lifts) != 2 or {x.get("name") for x in lifts} != {"g3b", "h3b"}:
        raise ValueError("Requires exact mmgroup 3B source normalizer manifest")

    gens = {}
    for lift in lifts:
        phase = lift.get("central_image")
        if not isinstance(phase, int) or phase not in (-1, 1):
            raise ValueError("Missing or invalid source central phase in manifest")
        gens[lift["name"]] = (monster_matrix(lift), phase % 3)

    c_atlas, d_atlas = atlas(root)
    Ic = eye()
    mc = neg(Ic)

    # 1. Enumerate base words up to depth
    base_words = enumerate_words(gens, max_base_states, depth)

    # 2. Extract powered C and D candidates
    # C candidates: phase = 2, M^2 = -I_12 (order 4)
    # D candidates: phase = 1, M^3 = I_12, M != I_12 (order 3)
    c_candidates = []
    d_candidates = []
    seen_c_mats = {}
    seen_d_mats = {}

    for base_mat, base_phase, w in base_words:
        if time.time() - start_time > time_limit:
            break
        # Compute order of base_mat
        cur = base_mat
        order = 1
        while cur != Ic and order <= max_power:
            cur = mul(cur, base_mat)
            order += 1
        if cur != Ic:
            continue

        # Power traversal
        cur = base_mat
        phase = base_phase
        for p in range(1, order):
            # Check C
            if phase == 2 and powm(cur, 2) == mc:
                key = freeze(cur)
                if key not in seen_c_mats:
                    cand = (cur, w, p)
                    c_candidates.append(cand)
                    seen_c_mats[key] = cand

            # Check D
            if phase == 1 and powm(cur, 3) == Ic and cur != Ic:
                key = freeze(cur)
                if key not in seen_d_mats:
                    cand = (cur, w, p)
                    d_candidates.append(cand)
                    seen_d_mats[key] = cand

            cur = mul(cur, base_mat)
            phase = (phase * base_phase) % 3

    # 3. Test candidate pairs
    tested_pairs = 0
    relation_passing_pairs = 0
    hits = []
    hit_budget_or_time = False

    for ca, wa, pa in c_candidates:
        if hit_budget_or_time:
            break
        for db, wb, pb in d_candidates:
            if time.time() - start_time > time_limit:
                hit_budget_or_time = True
                break
            if tested_pairs >= max_pairs:
                hit_budget_or_time = True
                break

            tested_pairs += 1

            # Fast screening: (CD)^28 == -I_12
            cd = mul(ca, db)
            if powm(cd, 28) != mc:
                continue

            # Full semipresentation and order-7 relator check
            if not source_relations(ca, db):
                continue

            relation_passing_pairs += 1

            # Intertwiner gate with exact symplectic similitude forms
            res = check_pair((c_atlas, d_atlas), (ca, db), actual_forms=True)
            if res.get("invertible_basis_witness") and res.get("form_transport_passed"):
                hit_info = {
                    "C_candidate": format_powered_word(wa, pa),
                    "D_candidate": format_powered_word(wb, pb),
                    "intertwiner_dimension": res.get("intertwiner_dimension"),
                    "T_rank": res.get("T_rank"),
                    "T_rows_F3": res.get("T_rows_F3"),
                    "form_transport_passed": res.get("form_transport_passed"),
                    "form_scale_mod3": res.get("form_scale_mod3"),
                    "cocycle_defect_ranks": res.get("cocycle_defect_ranks"),
                    "quadratic_central_corrections_derived": res.get("quadratic_central_corrections_derived"),
                    "provenance": "CANDIDATE_ONLY_unverified_original_quotient_word_identification",
                }
                hits.append(hit_info)

    duration = time.time() - start_time

    if len(hits) > 0:
        status = "CANDIDATES"
    elif hit_budget_or_time:
        status = "PARTIAL_NO_HITS"
    else:
        status = "NO_HITS_WITHIN_BOUNDS"

    return {
        "schema": "monster3b-powered-quotient-search-v1",
        "status": status,
        "duration_seconds": round(duration, 4),
        "depth": depth,
        "max_base_states": max_base_states,
        "max_power": max_power,
        "max_pairs": max_pairs,
        "time_limit": time_limit,
        "enumerated_base_words": len(base_words),
        "distinct_C_candidates": len(c_candidates),
        "distinct_D_candidates": len(d_candidates),
        "pairs_tested": tested_pairs,
        "relation_passing_pairs": relation_passing_pairs,
        "candidate_count": len(hits),
        "candidate_intertwiners": hits,
        "exhausted_budget_or_timed_out": hit_budget_or_time,
        "original_ATLAS_quotient_isomorphism_proved": False,
        "actual_Monster_element_words_rechecked_in_mmgroup": False,
        "selected_Hom_and_VOA_promoted": False,
    }

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True,
                        help="Path to monster3b-authentic-manifest.json")
    parser.add_argument("--depth", type=int, default=4,
                        help="Base word exploration depth (default: 4)")
    parser.add_argument("--max-base-states", type=int, default=3000,
                        help="Max base word states (default: 3000)")
    parser.add_argument("--max-power", type=int, default=120,
                        help="Max power for cyclic subgroup traversal (default: 120)")
    parser.add_argument("--max-pairs", type=int, default=10000,
                        help="Max pairs to examine (default: 10000)")
    parser.add_argument("--time-limit", type=float, default=90.0,
                        help="Execution time limit in seconds (default: 90)")
    parser.add_argument("--out", type=Path,
                        help="Output JSON file path")
    parser.add_argument("--root", type=Path, default=REPO_ROOT,
                        help="Repository root directory")

    args = parser.parse_args()

    result = run_powered_search(
        manifest_path=args.manifest,
        root=args.root,
        depth=args.depth,
        max_base_states=args.max_base_states,
        max_power=args.max_power,
        max_pairs=args.max_pairs,
        time_limit=args.time_limit,
    )

    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(encoded)

    print(encoded, end="")

if __name__ == "__main__":
    main()
