#!/usr/bin/env python3
"""Run the existing Monster 3B original GAP/CTblLib endpoint producers together.

This is a SOURCE execution handoff, not a new algebra/model:
  1. monster_3b_suzuki_main_quotient_match.g: original all-78 search,
     diagonal C3 descent, genuine 3B central phase and Monster occurrence;
  2. monster3b_atlas_suz2b_monster_4class_source_fusion.g: exact stored
     2.Suz.2 -> 6.Suz.2 -> main -> MN3B -> Monster class fusion.

Every invocation writes fresh isolated input/output/log files. Previous
build/ receipts are never overwritten or silently reused. Failure retains
a machine-readable receipt and the complete GAP log.

Run from anywhere (from repo root is conventional):
  python3 scripts/run_monster3b_gap_endpoint.py --timeout 900

This does NOT match a specific mmgroup generator word to a table class,
supply complex Monster matrices, or resolve absolute zeta orientation.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time
import traceback


MAIN_SOURCE = "scripts/monster_3b_suzuki_main_quotient_match.g"
FUSION_SOURCE = "scripts/monster3b_atlas_suz2b_monster_4class_source_fusion.g"
MAIN_PATH = "build/monster_3b_suzuki_main_quotient_match.json"
FUSION_PATH = "build/monster3b_atlas_suz2b_monster_4class_source_fusion.json"


def hash_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def stage_source(original: Path, literal_output: str, run_output: Path, staged: Path) -> str:
    data = original.read_text(encoding="utf-8")
    needle = json.dumps(literal_output)
    if data.count(needle) != 1:
        raise ValueError(f"{original.name}: expected exactly one output path {needle!r}, "
                         f"found {data.count(needle)}")
    data = data.replace(needle, json.dumps(run_output.as_posix()), 1)
    staged.write_text(data, encoding="utf-8")
    return hash_file(original)


def load_validator(repo: Path):
    source = repo / "scripts/render_monster_3b_suzuki_main_quotient_match.py"
    spec = importlib.util.spec_from_file_location("monster3b_main_receipt_validator", source)
    if spec is None or spec.loader is None:
        raise RuntimeError("original Suzuki/main receipt validator not importable")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.validate, hash_file(source)


def strict_main_receipt(data: dict, validate) -> dict:
    core = validate(data)  # original complete 210-class and cyclotomic-row schema
    if data["qg_to_n3b_kernel_order_three_class_position"] != 20:
        raise ValueError("main diagonal quotient kernel is not published class 20")
    if data["base_1458_extraspecial_central_class_position"] == 20:
        raise ValueError("extraspecial 3B centre was confused with diagonal class 20")
    for prefix, degree in (("12", 17496), ("78", 113724)):
        positions = data[f"main_{prefix}_split_positions"]
        values = data[f"main_{prefix}_class20_trace_values"]
        selected = data[f"main_{prefix}_class20_selected_position"]
        descending = data[f"main_{prefix}_descending_position"]
        if len(positions) != 2 or len(values) != 2:
            raise ValueError(f"{prefix}: expected two original main constituent rows")
        if sorted(values) != [-degree // 2, degree]:
            raise ValueError(f"{prefix}: class20 K-kernel trace pair inconsistent: {values}")
        if selected != descending or selected not in positions:
            raise ValueError(f"{prefix}: one-class and full MN3B descent select different rows")
        idx = positions.index(selected)
        if values[idx] != degree:
            raise ValueError(f"{prefix}: selected row has nontrivial diagonal K phase")
        if data[f"main_{prefix}_selected_extraspecial_c3_trace"] != -degree // 2:
            raise ValueError(f"{prefix}: source 3B-centre paired-phase trace mismatch")
    if (data.get("two_distinct_c3_source_projectors_agree_with_full_character_descent") is not True
            or data.get("selected_12_78_equal_c3_phase_pair_count_exactly_two") is not True
            or data["common_729_necessary_equal_C3_phase_pair_count"] != 2):
        raise ValueError("selected 12 and 78 do not share original double-C3 phase constraint")

    # New GAP receipt coordinates are source 6.Suz Irr positions, not a
    # chosen Monster/mmgroup generator word. Preserve existing older receipts
    # (which reported the exact family but not literal pair membership).
    pair_keys = (
        "six_suz_same_c3_12_to_78_irr_pairs",
        "six_suz_direct_sym2_12_to_78_irr_pairs",
        "six_suz_dual_sym2_12_to_78_irr_pairs",
        "selected_same_c3_90_is_12_plus_dual_sym2_12",
    )
    pair_metadata = {}
    if any(key in data for key in pair_keys):
        if not all(key in data for key in pair_keys):
            raise ValueError("incomplete source 12/78 original Irr pairing records")
        def pairs(key):
            raw = data[key]
            if (not isinstance(raw, list) or len(raw) not in (0, 2)
                or any(not isinstance(p, list) or len(p) != 2 or
                       any(type(n) is not int for n in p)
                       for p in raw)):
                raise ValueError(f"invalid source Irr pairing list: {key}")
            if any(p[0] not in data["six_suz_degree12_positions"] or
                   p[1] not in data["six_suz_degree78_positions"] for p in raw):
                raise ValueError(f"source Irr pair outside selected 12/78 characters: {key}")
            if len({tuple(p) for p in raw}) != 2:
                raise ValueError(f"duplicated 12/78 pairing in {key}")
            return raw
        same = pairs(pair_keys[0])
        direct = pairs(pair_keys[1])
        dual = pairs(pair_keys[2])
        selected_dual = data[pair_keys[3]]
        if type(selected_dual) is not bool:
            raise ValueError("selected same-C3 dual Sym2 bit must be boolean")
        if core["full_nebe"]:
            if (len(same) != 2 or len(direct) != 2 or len(dual) != 2 or
                selected_dual is not True or
                {tuple(x) for x in same} != {tuple(x) for x in dual} or
                {tuple(x) for x in same} & {tuple(x) for x in direct}):
                raise ValueError("selected Nebe Sym2 same-C3 and dual-Sym2 maps disagree")
        pair_metadata = {
            "same_c3_12_to_78_irr_position_pairs": same,
            "direct_sym2_12_to_78_irr_position_pairs": direct,
            "dual_sym2_12_to_78_irr_position_pairs": dual,
            "selected_same_c3_90_is_12_plus_dual_sym2_12": selected_dual,
        }

    faithful = core["selected_faithful"]
    sym2 = core["full_nebe"]
    # Faithfulness and the original complete Sym^2 comparison are distinct
    # outcomes; do NOT infer Sym^2 merely from nonfaithfulness.
    family = ("FAITHFUL_78" if faithful else
              "NEBE_SYM2_78_OR_DUAL" if sym2 else
              "OTHER_NONFAITHFUL_78")
    return {
        "status": "SOURCE_GAP_MATCH_CONFIRMED",
        "original_source_selection": {
            "selected_78_family": family,
            "selected_78_faithful": faithful,
            "selected_78_is_nebe_sym2_full_character_equal": sym2,
            "selected_12_labels": data["degree_12_atlas_labels"],
            "selected_78_labels": data["degree_78_atlas_labels"],
            "selected_12_irr_positions": data["six_suz_degree12_positions"],
            "selected_78_irr_positions": data["six_suz_degree78_positions"],
            "selected_12_c2_plus_78_c2_trace": core["source_trace"],
            "source_78_vs_sym2_trace": core["sym2_trace"],
            "same_c3_phase_pairings_count": 2,
            **pair_metadata,
        },
        "original_group_tables": {
            "main": data["main_table"],
            "mn3b": data["mn3b_table"],
            "six_suz": data["six_suz_table"],
            "gap_version": data["gap_runtime_version"],
            "ctbllib_version": data["ctbllib_runtime_version"],
            "main_diagonal_c3_kernel_class": 20,
            "main_extraspecial_z3b_class": data["base_1458_extraspecial_central_class_position"],
            "main_12_class20_pair": data["main_12_class20_trace_values"],
            "main_78_class20_pair": data["main_78_class20_trace_values"],
            "main_12_descending_position": data["main_12_descending_position"],
            "main_78_descending_position": data["main_78_descending_position"],
            "mn3b_12_irr_position": data["mn3b_12_position"],
            "mn3b_78_irr_position": data["mn3b_78_position"],
            "mn3b_12_monster_multiplicity": data["mn3b_12_monster_multiplicity"],
            "mn3b_78_monster_multiplicity": data["mn3b_78_monster_multiplicity"],
            "extraspecial_selected_12_c3_trace": data["main_12_selected_extraspecial_c3_trace"],
            "extraspecial_selected_78_c3_trace": data["main_78_selected_extraspecial_c3_trace"],
        },
        "absolute_zeta_orientation_identified": False,
        "actual_MM_generator_word_to_source_H_identified": False,
        "numerical_complex_12_78_operators_constructed": False,
    }


def strict_fusion_receipt(data: dict) -> dict:
    if data.get("schema") != "monster3b-atlas-source-Suz2B-to-Monster4-fusion-v1":
        raise ValueError("unexpected original four-class fusion schema")
    rows = data.get("candidates")
    if not isinstance(rows, list) or not rows:
        raise ValueError("no source four-class fusion candidates")
    labels = data.get("all_possible_monster_four_labels")
    if not isinstance(labels, list) or not set(labels) <= {"4A", "4C", "4D"}:
        raise ValueError("source Monster four-class labels invalid")
    observed = sorted({x["monster_four_label"] for x in rows})
    if observed != sorted(set(labels)):
        raise ValueError("source four-class candidates/label inventory inconsistent")
    unique = len(observed) == 1
    if data.get("actual_monster_four_class_uniquely_forced_by_class_fusions") is not unique:
        raise ValueError("source four-class uniqueness boolean mismatch")
    if data.get("status") != ("UNIQUE_SOURCE_FUSION" if unique else "AMBIGUOUS_SOURCE_FUSION"):
        raise ValueError("source four-class status inconsistent")
    if data.get("literal_source_word_2Suz_class_individually_identified") is not False:
        raise ValueError("source class fusion cannot identify the user-local mmgroup word")
    return {
        "status": data["status"],
        "source_four_class_labels": observed,
        "source_four_class_rows": rows,
        "source_four_class_is_unique": unique,
        "mmgroup_word_to_four_class_identified": False,
    }


def run_gap(gap: str, source: Path, label: str, outdir: Path,
            timeout: int, root: Path) -> dict:
    command = [gap, "-q", str(source)]
    t0 = time.monotonic()
    try:
        proc = subprocess.run(command, cwd=root, stdin=subprocess.DEVNULL,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                              text=True, errors="replace", timeout=timeout,
                              check=False)
        log = proc.stdout
        status = "EXIT_0" if proc.returncode == 0 else f"EXIT_{proc.returncode}"
    except subprocess.TimeoutExpired as exc:
        log = (exc.stdout or b"").decode("utf-8", "replace") if isinstance(exc.stdout, bytes) else (exc.stdout or "")
        log += "\nTIMEOUT: GAP run exceeded --timeout seconds\n"
        status = "TIMEOUT"
    log_file = outdir / f"{label}.log"
    log_file.write_text(log, encoding="utf-8")
    return {"status": status, "duration_seconds": round(time.monotonic()-t0, 3),
            "command": command, "log": str(log_file),
            "log_tail": log[-3000:] if status != "EXIT_0" else None}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--outdir", type=Path, default=None,
                        help="unique output directory; default build/monster3b-gap-endpoint/RUN-ID")
    parser.add_argument("--timeout", type=int, default=900,
                        help="per-GAP-stage timeout seconds (default 900)")
    parser.add_argument("--skip-fusion", action="store_true",
                        help="run just original 6.Suz full-character selection")
    args = parser.parse_args()
    if args.timeout < 1:
        parser.error("--timeout must be positive")
    root = args.root.resolve()
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    outdir = ((root / "build/monster3b-gap-endpoint" / f"run-{stamp}-{__import__('os').getpid()}")
              if args.outdir is None else args.outdir.resolve())
    if outdir.exists() and any(outdir.iterdir()):
        parser.error(f"refusing to reuse populated output directory: {outdir}")
    outdir.mkdir(parents=True, exist_ok=True)
    output = {
        "schema": "monster3b-original-GAP-endpoint-run-v1",
        "status": "NOT_RUN",
        "output_dir": str(outdir),
        "stages": {},
        "sources": {},
        "original_selected_character_attached_to_MM_word": False,
        "original_characteristic_zero_Monster_matrices_computed": False,
        "user_followup_required": "Return endpoint_summary.json and main_gap.log; if fusion ran, also fusion_gap.log",
    }
    receipt = outdir / "endpoint_summary.json"
    try:
        executable = shutil.which("gap")
        if executable is None:
            raise RuntimeError("GAP not found in PATH; install/load GAP with CTblLib first")
        validator, validator_sha = load_validator(root)
        output["sources"]["original_main_validator_sha256"] = validator_sha

        main_src = root / MAIN_SOURCE
        main_json = outdir / "original_main_character_receipt.json"
        main_staged = outdir / "staged_main.g"
        main_sha = stage_source(main_src, MAIN_PATH, main_json, main_staged)
        output["sources"]["original_main_GAP_sha256"] = main_sha
        output["stages"]["main"] = run_gap(
            executable, main_staged, "main_gap", outdir, args.timeout, root)
        if output["stages"]["main"]["status"] != "EXIT_0" or not main_json.is_file():
            raise RuntimeError("original main GAP stage failed or did not write a fresh receipt")
        data = json.loads(main_json.read_text(encoding="utf-8"))
        output["main"] = strict_main_receipt(data, validator)
        output["sources"]["original_main_receipt_sha256"] = hash_file(main_json)
        output["status"] = "MAIN_SOURCE_MATCHED"

        if not args.skip_fusion:
            fusion_src = root / FUSION_SOURCE
            fusion_json = outdir / "original_four_class_fusion_receipt.json"
            fusion_staged = outdir / "staged_four_class_fusion.g"
            output["sources"]["original_fusion_GAP_sha256"] = stage_source(
                fusion_src, FUSION_PATH, fusion_json, fusion_staged)
            output["stages"]["fusion"] = run_gap(
                executable, fusion_staged, "fusion_gap", outdir, args.timeout, root)
            if output["stages"]["fusion"]["status"] != "EXIT_0" or not fusion_json.is_file():
                raise RuntimeError("original four-class GAP stage failed or did not write a fresh receipt")
            fusion = json.loads(fusion_json.read_text(encoding="utf-8"))
            output["fusion"] = strict_fusion_receipt(fusion)
            output["sources"]["original_fusion_receipt_sha256"] = hash_file(fusion_json)
            output["status"] = "MAIN_AND_FUSION_SOURCE_MATCHED"
    except Exception as exc:
        output["failure"] = {"type": type(exc).__name__,
                             "message": str(exc),
                             "traceback": traceback.format_exc(limit=5)}
        output["status"] = ("PARTIAL_MAIN_MATCHED_FUSION_INCOMPLETE"
                            if "main" in output else "ERROR_FAIL_CLOSED")
    finally:
        receipt.write_text(json.dumps(output, indent=2, sort_keys=True, ensure_ascii=False)+"\n",
                           encoding="utf-8")
        print("\nMonster 3B original GAP endpoint:", output["status"])
        if "main" in output:
            selected = output["main"]["original_source_selection"]
            print("Selected degree-78 family:", selected["selected_78_family"])
            print("12 labels:", selected["selected_12_labels"],
                  "78 labels:", selected["selected_78_labels"])
            print("Selected C2 trace:", selected["selected_12_c2_plus_78_c2_trace"],
                  "common C3 pairings:", selected["same_c3_phase_pairings_count"])
        if "fusion" in output:
            print("Monster four-class labels:", output["fusion"]["source_four_class_labels"])
        if "failure" in output:
            print("Failure:", output["failure"]["message"], file=sys.stderr)
            for stage in output["stages"].values():
                if stage.get("log_tail"):
                    print(stage["log_tail"], file=sys.stderr)
        print("RECEIPT:", receipt)
        print("No mmgroup-word or complex-operator identification is implied.")
    return 0 if output["status"] in ("MAIN_SOURCE_MATCHED", "MAIN_AND_FUSION_SOURCE_MATCHED") else 2


if __name__ == "__main__":
    raise SystemExit(main())
