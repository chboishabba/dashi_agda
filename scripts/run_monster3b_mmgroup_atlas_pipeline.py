#!/usr/bin/env python3
"""Monster 3B mmgroup -> ATLAS pipeline runner.

Orchestrates the 4-stage pipeline connecting the 2026 Dietrich-Lee-Pisani-Popiel
Monster 3B normalizer generator realization in mmgroup with the Norton-Wilson /
ATLAS 2.Suz:2 GF(3) symplectic representation.

Stages:
  selftest: Pure GF(3) and ATLAS gate selftests (no mmgroup execution required).
  extract:  Extract authentic Monster E/Z(E) generators via mmgroup and MMV(7).
  search:   Bounded word search for ATLAS C, D candidates in Monster E/Z(E).
  verify:   Exact GF(3) intertwiner and symplectic similitude verification.

Outputs are written to .dashi/monster3b-mmgroup/.
"""

import argparse
import hashlib
import json
import os
import signal
import sys
import time
from pathlib import Path

# Add scripts directory to sys.path so modules can import each other
SCRIPTS_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPTS_DIR.parent
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))

DEFAULT_OUT_DIR = REPO_ROOT / ".dashi" / "monster3b-mmgroup"

def sha256_file(path: Path) -> str:
    if not path.is_file():
        return "MISSING"
    return hashlib.sha256(path.read_bytes()).hexdigest()

def get_provenance_hashes(root: Path) -> dict:
    files = {
        "script_pipeline": root / "scripts" / "run_monster3b_mmgroup_atlas_pipeline.py",
        "script_extract": root / "scripts" / "monster_3b_mmgroup_source_symplectic_basis.py",
        "script_search": root / "scripts" / "monster3b_atlas_mmgroup_bounded_word_search.py",
        "script_gate": root / "scripts" / "monster3b_atlas_mmgroup_cross_source_intertwiner_gate.py",
        "script_weyl": root / "scripts" / "monster_3b_mmgroup_weyl_word_alignment.py",
        "atlas_m1": root / "data" / "atlas" / "2Suzd2G1-f3r12aB0.m1",
        "atlas_m2": root / "data" / "atlas" / "2Suzd2G1-f3r12aB0.m2",
    }
    return {k: sha256_file(v) for k, v in files.items()}

class TimeoutHandler:
    def __init__(self, seconds: int):
        self.seconds = seconds

    def __enter__(self):
        if self.seconds > 0 and hasattr(signal, "SIGALRM"):
            signal.signal(signal.SIGALRM, self._handle_timeout)
            signal.alarm(self.seconds)
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        if self.seconds > 0 and hasattr(signal, "SIGALRM"):
            signal.alarm(0)

    def _handle_timeout(self, signum, frame):
        raise TimeoutError(f"Stage execution exceeded timeout of {self.seconds} seconds")

def load_or_init_pipeline_receipt(out_dir: Path, root: Path) -> dict:
    receipt_file = out_dir / "pipeline-receipt.json"
    if receipt_file.is_file():
        try:
            data = json.loads(receipt_file.read_text())
            if isinstance(data, dict) and data.get("schema") == "monster3b-mmgroup-atlas-pipeline-receipt-v1":
                return data
        except Exception:
            pass
    return {
        "schema": "monster3b-mmgroup-atlas-pipeline-receipt-v1",
        "repo_root": str(root),
        "created_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "provenance_hashes": get_provenance_hashes(root),
        "stages": {},
    }

def save_pipeline_receipt(out_dir: Path, receipt: dict):
    out_dir.mkdir(parents=True, exist_ok=True)
    receipt_file = out_dir / "pipeline-receipt.json"
    receipt["last_updated_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    receipt_file.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")

def run_selftest(root: Path, out_dir: Path, timeout: int = 0) -> dict:
    from monster3b_atlas_mmgroup_cross_source_intertwiner_gate import test as gate_test
    from monster_3b_mmgroup_source_symplectic_basis import selftest as basis_selftest

    start_time = time.time()
    with TimeoutHandler(timeout):
        gate_res = gate_test(root)
        basis_res = basis_selftest()

    duration = time.time() - start_time
    status = "PASS" if (gate_res.get("status") == "PASS_GF3_SAME_SOURCE_FIXTURE" and
                        basis_res.get("status") == "local_pure_F3_symplectic_selftest") else "FAIL"

    result = {
        "stage": "selftest",
        "status": status,
        "duration_seconds": round(duration, 4),
        "gate_selftest": gate_res,
        "basis_selftest": basis_res,
    }
    return result

def run_extract(root: Path, out_dir: Path, timeout: int = 900) -> tuple[dict, dict]:
    from monster_3b_mmgroup_source_symplectic_basis import run as extract_run

    start_time = time.time()
    with TimeoutHandler(timeout):
        manifest, source_receipt = extract_run()

    duration = time.time() - start_time
    manifest_path = out_dir / "monster3b-authentic-manifest.json"
    source_receipt_path = out_dir / "monster3b-source-receipt.json"

    out_dir.mkdir(parents=True, exist_ok=True)
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    source_receipt_path.write_text(json.dumps(source_receipt, indent=2) + "\n")

    pipeline_stage_result = {
        "stage": "extract",
        "status": "PASS" if source_receipt.get("observed_actual_mmgroup_execution") else "FAIL",
        "duration_seconds": round(duration, 4),
        "manifest_path": str(manifest_path),
        "source_receipt_path": str(source_receipt_path),
        "rank_commutator_form": source_receipt.get("rank_commutator_form"),
        "normalizer_generators": source_receipt.get("normalizer_generators"),
        "mmgroup_version": source_receipt.get("mmgroup_version"),
        "actual_MMV7_nonzero_zeta_samples": source_receipt.get("actual_MMV7_nonzero_zeta_samples"),
    }
    return pipeline_stage_result, source_receipt

def run_search(root: Path, out_dir: Path, depth: int, max_states: int, max_pairs: int, timeout: int = 900) -> dict:
    from monster3b_atlas_mmgroup_bounded_word_search import search as word_search
    from monster3b_atlas_mmgroup_cross_source_intertwiner_gate import atlas, monster_matrix

    manifest_path = out_dir / "monster3b-authentic-manifest.json"
    if not manifest_path.is_file():
        raise FileNotFoundError(f"Missing extract manifest: {manifest_path}. Run --stage extract first.")

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

    atlas_pair = atlas(root)

    start_time = time.time()
    with TimeoutHandler(timeout):
        search_result = word_search(atlas_pair, gens, depth, max_states, max_pairs)

    duration = time.time() - start_time
    search_path = out_dir / "monster3b-bounded-search.json"
    out_dir.mkdir(parents=True, exist_ok=True)
    search_path.write_text(json.dumps(search_result, indent=2, sort_keys=True) + "\n")

    hits = search_result.get("candidate_intertwiners", [])
    pipeline_stage_result = {
        "stage": "search",
        "status": "PASS" if len(hits) > 0 else "NO_HITS",
        "duration_seconds": round(duration, 4),
        "search_path": str(search_path),
        "depth": depth,
        "max_states": max_states,
        "max_pairs": max_pairs,
        "candidate_count": len(hits),
        "relation_filtered_pairs_tested": search_result.get("relation_filtered_pairs_tested"),
        "C_square_negative_I_candidate_count": search_result.get("C_square_negative_I_candidate_count"),
        "D_cube_identity_candidate_count": search_result.get("D_cube_identity_candidate_count"),
    }
    return pipeline_stage_result, search_result

def run_verify(root: Path, out_dir: Path, candidate_index: int = 0, timeout: int = 900) -> tuple[dict, dict]:
    from monster3b_atlas_mmgroup_cross_source_intertwiner_gate import (
        atlas, candidate_word, check_pair, monster_matrix
    )

    manifest_path = out_dir / "monster3b-authentic-manifest.json"
    search_path = out_dir / "monster3b-bounded-search.json"

    if not manifest_path.is_file():
        raise FileNotFoundError(f"Missing extract manifest: {manifest_path}. Run --stage extract first.")
    if not search_path.is_file():
        raise FileNotFoundError(f"Missing search output: {search_path}. Run --stage search first.")

    manifest = json.loads(manifest_path.read_text())
    search_data = json.loads(search_path.read_text())
    candidates = search_data.get("candidate_intertwiners", [])

    if not candidates:
        raise ValueError("No candidates found in search output to verify.")
    if candidate_index < 0 or candidate_index >= len(candidates):
        raise IndexError(f"Candidate index {candidate_index} out of range [0, {len(candidates)-1}]")

    cand = candidates[candidate_index]
    c_word = cand.get("C_word")
    d_word = cand.get("D_word")

    lifts = manifest.get("normalizer_lifts", [])
    gens = {}
    for lift in lifts:
        lam = lift.get("central_image")
        gens[lift["name"]] = (monster_matrix(lift), lam % 3)

    target_c, phase_c = candidate_word(c_word, gens)
    target_d, phase_d = candidate_word(d_word, gens)

    if (phase_c, phase_d) != (2, 1):
        raise ValueError(f"Centre-multiplier generator mismatch: expected (2, 1), got ({phase_c}, {phase_d})")

    c_atlas, d_atlas = atlas(root)

    start_time = time.time()
    with TimeoutHandler(timeout):
        verify_result = check_pair((c_atlas, d_atlas), (target_c, target_d), actual_forms=True)

    duration = time.time() - start_time
    verify_result["candidate_index"] = candidate_index
    verify_result["candidate_C_word"] = c_word
    verify_result["candidate_D_word"] = d_word
    verify_result["word_lengths"] = [len(c_word), len(d_word)]
    verify_result["source_normalizer_generator_names"] = ["g3b", "h3b"]
    verify_result["duration_seconds"] = round(duration, 4)

    verify_path = out_dir / "monster3b-cross-source-gate.json"
    out_dir.mkdir(parents=True, exist_ok=True)
    verify_path.write_text(json.dumps(verify_result, indent=2, sort_keys=True) + "\n")

    status = "PASS" if (verify_result.get("invertible_basis_witness") and
                        verify_result.get("form_transport_passed")) else "FAIL"

    pipeline_stage_result = {
        "stage": "verify",
        "status": status,
        "duration_seconds": round(duration, 4),
        "verify_path": str(verify_path),
        "candidate_index": candidate_index,
        "intertwiner_dimension": verify_result.get("intertwiner_dimension"),
        "form_transport_passed": verify_result.get("form_transport_passed"),
        "form_scale_mod3": verify_result.get("form_scale_mod3"),
        "cocycle_defect_ranks": verify_result.get("cocycle_defect_ranks"),
    }
    return pipeline_stage_result, verify_result

def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--stage", required=True, choices=["selftest", "extract", "search", "verify"],
                        help="Pipeline stage to execute")
    parser.add_argument("--timeout", type=int, default=900,
                        help="Execution timeout in seconds (default: 900)")
    parser.add_argument("--depth", type=int, default=4,
                        help="Bounded search word depth (default: 4)")
    parser.add_argument("--max-states", type=int, default=20000,
                        help="Bounded search max quotient matrix states (default: 20000)")
    parser.add_argument("--max-pairs", type=int, default=100,
                        help="Bounded search max filtered pairs to test (default: 100)")
    parser.add_argument("--candidate-index", type=int, default=0,
                        help="Candidate index to verify from search hits (default: 0)")
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR,
                        help=f"Output directory for receipts and manifests (default: {DEFAULT_OUT_DIR})")
    parser.add_argument("--root", type=Path, default=REPO_ROOT,
                        help=f"Repository root directory (default: {REPO_ROOT})")

    args = parser.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)

    pipeline_receipt = load_or_init_pipeline_receipt(args.out_dir, args.root)
    pipeline_receipt["provenance_hashes"] = get_provenance_hashes(args.root)

    print(f"=== Stage: {args.stage} ===")
    print(f"Output directory: {args.out_dir}")

    try:
        if args.stage == "selftest":
            stage_res = run_selftest(args.root, args.out_dir, timeout=args.timeout)
            pipeline_receipt["stages"]["selftest"] = stage_res
            save_pipeline_receipt(args.out_dir, pipeline_receipt)
            print(json.dumps(stage_res, indent=2))
            if stage_res["status"] != "PASS":
                sys.exit(1)

        elif args.stage == "extract":
            stage_res, source_receipt = run_extract(args.root, args.out_dir, timeout=args.timeout)
            pipeline_receipt["stages"]["extract"] = stage_res
            save_pipeline_receipt(args.out_dir, pipeline_receipt)
            print(json.dumps(source_receipt, indent=2))
            if stage_res["status"] != "PASS":
                sys.exit(1)

        elif args.stage == "search":
            stage_res, search_res = run_search(
                args.root, args.out_dir, depth=args.depth, max_states=args.max_states,
                max_pairs=args.max_pairs, timeout=args.timeout
            )
            pipeline_receipt["stages"]["search"] = stage_res
            save_pipeline_receipt(args.out_dir, pipeline_receipt)
            print(json.dumps(search_res, indent=2))
            if stage_res["status"] not in ("PASS", "NO_HITS"):
                sys.exit(1)

        elif args.stage == "verify":
            stage_res, verify_res = run_verify(
                args.root, args.out_dir, candidate_index=args.candidate_index, timeout=args.timeout
            )
            pipeline_receipt["stages"]["verify"] = stage_res
            save_pipeline_receipt(args.out_dir, pipeline_receipt)
            print(json.dumps(verify_res, indent=2))
            if stage_res["status"] != "PASS":
                sys.exit(1)

    except Exception as exc:
        err_res = {
            "stage": args.stage,
            "status": "ERROR",
            "error_type": type(exc).__name__,
            "error_message": str(exc),
            "timestamp_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        }
        pipeline_receipt["stages"][args.stage] = err_res
        save_pipeline_receipt(args.out_dir, pipeline_receipt)
        print(json.dumps(err_res, indent=2), file=sys.stderr)
        sys.exit(1)

if __name__ == "__main__":
    main()
