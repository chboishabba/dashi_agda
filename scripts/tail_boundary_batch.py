#!/usr/bin/env python3
"""Aggregate mdl-tail-boundary counts across compatible dashifine batches."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tempfile
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, List

from run_execution_contract_on_closure_csv import evaluate_closure_csv

ROOT_DIR = Path(__file__).resolve().parents[1]
DEFAULT_INPUTS = [
    "../dashifine/hepdata_lyapunov_test_out/dashi_idk_out.csv/closure_embedding_per_step.csv",
    "../dashifine/hepdata_lyapunov_test_out_new/dashi_idk_out/closure_embedding_per_step.csv",
    "../dashifine/hepdata_lyapunov_test_out_all/dashi_idk_out/closure_embedding_per_step.csv",
]

TAIL_CANDIDATE_TOKENS = (
    "ttbar",
    "mtt",
    "z_pt",
    "m4l",
    "pt4l",
    "hgg_pt",
    "dijet",
)

CONTROL_TOKENS = (
    "ptll",
    "pTll",
    "phistar",
)


def classify_family_cohort(name: str) -> str:
    lowered = name.lower()
    if any(token.lower() in lowered for token in TAIL_CANDIDATE_TOKENS):
        return "tail_candidate"
    if any(token.lower() in lowered for token in CONTROL_TOKENS):
        return "negative_control"
    return "unclassified"


def resolve_from_root(path_str: str) -> Path:
    path = Path(path_str)
    return path if path.is_absolute() else (ROOT_DIR / path)


def run_harness(input_path: Path, jmd_table: Path, dasl_source_repo: Path, tmpdir: Path) -> Dict[str, object]:
    safe_stem = input_path.parts[-3] if len(input_path.parts) >= 3 else input_path.stem
    family_json = tmpdir / f"{safe_stem}-family.json"
    summary_json = tmpdir / f"{safe_stem}-tail-summary.json"
    cmd = [
        sys.executable,
        str(ROOT_DIR / "scripts" / "regime_test.py"),
        "cone",
        str(input_path),
        "--preset",
        "dashifine-closure-embedding",
        "--arrow-profile",
        "strict",
        "--jmd-table",
        str(jmd_table),
        "--dasl-source-repo",
        str(dasl_source_repo),
        "--emit-family-witness-json",
        str(family_json),
        "--emit-tail-boundary-summary-json",
        str(summary_json),
        "--top-n",
        "0",
    ]
    subprocess.run(cmd, cwd=ROOT_DIR, check=True, capture_output=True, text=True)
    return {
        "family_rows": json.loads(family_json.read_text(encoding="utf-8")),
        "tail_summary": json.loads(summary_json.read_text(encoding="utf-8")),
    }


def run_execution_contract(input_path: Path, tmpdir: Path) -> Dict[str, object]:
    safe_stem = input_path.parts[-3] if len(input_path.parts) >= 3 else input_path.stem
    receipts_csv = tmpdir / f"{safe_stem}-execution-receipts.csv"
    _, summary = evaluate_closure_csv(
        input_path,
        label_col="label",
        step_col="step",
        arrow_col="v_arrow",
        x_cols=["v_pnorm", "v_dnorm", "v_depth"],
        mask=[1.0, 1.0, -1.0],
        eps_arrow=1e-9,
        eps_cone=1e-9,
        min_eigen_overlap=0.80,
        basin_radius=10.0,
        out_path=receipts_csv,
    )
    return {
        "receipts_csv": str(receipts_csv),
        "summary": summary,
    }


def summarize_batch(inputs: List[Path], jmd_table: Path, dasl_source_repo: Path) -> Dict[str, object]:
    batch_rows: List[Dict[str, object]] = []
    unique_family_occurrences: Dict[str, List[Dict[str, object]]] = defaultdict(list)
    class_counter: Counter[str] = Counter()
    mdl_tail_instances = 0

    with tempfile.TemporaryDirectory(prefix="tail-boundary-batch-") as raw_tmp:
        tmpdir = Path(raw_tmp)
        for input_path in inputs:
            result = run_harness(input_path, jmd_table, dasl_source_repo, tmpdir)
            execution_contract = run_execution_contract(input_path, tmpdir)
            family_rows = result["family_rows"]
            tail_summary = result["tail_summary"]
            batch_entry = {
                "input": str(input_path),
                "family_count": len(family_rows),
                "tail_boundary_summary": tail_summary,
                "execution_contract": execution_contract,
                "families": family_rows,
            }
            batch_rows.append(batch_entry)
            for row in family_rows:
                family = str(row["family"])
                klass = str(row["family_class"])
                class_counter[klass] += 1
                if klass == "mdl_tail_boundary":
                    mdl_tail_instances += 1
                unique_family_occurrences[family].append(
                    {
                        "input": str(input_path),
                        "family_class": klass,
                        "tail_localized": row.get("tail_localized"),
                        "terminal_boundary": row.get("terminal_boundary"),
                        "cone_ok": row.get("cone_ok"),
                        "fejer_ok": row.get("fejer_ok"),
                        "closest_ok": row.get("closest_ok"),
                        "mdl_exact_ok": row.get("mdl_exact_ok"),
                    }
                )

    mdl_families = {
        family: occurrences
        for family, occurrences in unique_family_occurrences.items()
        if any(item["family_class"] == "mdl_tail_boundary" for item in occurrences)
    }
    mdl_family_names = sorted(mdl_families)
    mdl_occurrences = [
        item
        for occurrences in mdl_families.values()
        for item in occurrences
        if item["family_class"] == "mdl_tail_boundary"
    ]

    repeated_interior_controls: List[str] = []
    repeated_non_mdl_boundary_families: List[str] = []
    cohort_counts: Counter[str] = Counter()
    cohort_class_counts: Dict[str, Counter[str]] = defaultdict(Counter)
    family_cohorts: Dict[str, str] = {}
    tail_candidate_families: List[str] = []
    negative_control_families: List[str] = []
    unclassified_families: List[str] = []
    tail_candidate_boundary_families: List[str] = []
    tail_candidate_interior_families: List[str] = []

    for family, occurrences in sorted(unique_family_occurrences.items()):
        cohort = classify_family_cohort(family)
        family_cohorts[family] = cohort
        cohort_counts[cohort] += 1
        classes = [item["family_class"] for item in occurrences]
        unique_classes = sorted(set(classes))
        for klass in classes:
            cohort_class_counts[cohort][klass] += 1
        if cohort == "tail_candidate":
            tail_candidate_families.append(family)
            if any(klass != "interior_family" for klass in unique_classes):
                tail_candidate_boundary_families.append(family)
            else:
                tail_candidate_interior_families.append(family)
        elif cohort == "negative_control":
            negative_control_families.append(family)
        else:
            unclassified_families.append(family)
        if len(occurrences) >= 2 and all(klass == "interior_family" for klass in classes):
            repeated_interior_controls.append(family)
        if len(occurrences) >= 2 and all(
            klass != "mdl_tail_boundary" for klass in classes
        ) and any(klass != "interior_family" for klass in classes):
            repeated_non_mdl_boundary_families.append(family)

    next_priority_tail_families = [
        family
        for family in tail_candidate_boundary_families + tail_candidate_interior_families
        if family not in mdl_family_names
    ]

    return {
        "inputs": [str(path) for path in inputs],
        "batch_count": len(inputs),
        "compatible_step_file_count": len(inputs),
        "total_family_instances": sum(len(entry["families"]) for entry in batch_rows),
        "class_counts": dict(sorted(class_counter.items())),
        "mdl_tail_boundary_instance_count": mdl_tail_instances,
        "mdl_tail_boundary_unique_family_count": len(mdl_family_names),
        "mdl_tail_boundary_families": mdl_family_names,
        "mdl_tail_boundary_all_tail_localized": (
            all(item.get("tail_localized") is True for item in mdl_occurrences)
            if mdl_occurrences
            else None
        ),
        "mdl_tail_boundary_all_terminal_boundary": (
            all(item.get("terminal_boundary") is True for item in mdl_occurrences)
            if mdl_occurrences
            else None
        ),
        "mdl_tail_boundary_all_cone_ok": (
            all(item.get("cone_ok") is True for item in mdl_occurrences)
            if mdl_occurrences
            else None
        ),
        "mdl_tail_boundary_all_fejer_ok": (
            all(item.get("fejer_ok") is True for item in mdl_occurrences)
            if mdl_occurrences
            else None
        ),
        "mdl_tail_boundary_all_closest_ok": (
            all(item.get("closest_ok") is True for item in mdl_occurrences)
            if mdl_occurrences
            else None
        ),
        "mdl_tail_boundary_all_mdl_exact_fail": (
            all(item.get("mdl_exact_ok") is False for item in mdl_occurrences)
            if mdl_occurrences
            else None
        ),
        "family_cohorts": family_cohorts,
        "cohort_counts": dict(sorted(cohort_counts.items())),
        "cohort_class_counts": {
            cohort: dict(sorted(counter.items()))
            for cohort, counter in sorted(cohort_class_counts.items())
        },
        "tail_candidate_families": tail_candidate_families,
        "negative_control_families": negative_control_families,
        "unclassified_families": unclassified_families,
        "tail_candidate_boundary_families": tail_candidate_boundary_families,
        "tail_candidate_interior_families": tail_candidate_interior_families,
        "next_priority_tail_families": next_priority_tail_families,
        "repeated_interior_control_families": repeated_interior_controls,
        "repeated_non_mdl_boundary_families": repeated_non_mdl_boundary_families,
        "unique_family_occurrences": dict(sorted(unique_family_occurrences.items())),
        "batches": batch_rows,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Aggregate mdl-tail-boundary counts across compatible dashifine datasets"
    )
    parser.add_argument(
        "--inputs",
        nargs="*",
        default=DEFAULT_INPUTS,
        help="closure_embedding_per_step.csv inputs to aggregate",
    )
    parser.add_argument(
        "--jmd-table",
        default="artifacts/regime_test/jmd_regime_table.csv",
    )
    parser.add_argument(
        "--dasl-source-repo",
        default="../kant-zk-pastebin",
    )
    parser.add_argument(
        "--output",
        default="artifacts/regime_test/tail_boundary_batch_latest.json",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    inputs = [resolve_from_root(item) for item in args.inputs]
    jmd_table = resolve_from_root(args.jmd_table)
    dasl_source_repo = resolve_from_root(args.dasl_source_repo)
    summary = summarize_batch(inputs, jmd_table, dasl_source_repo)
    output_path = resolve_from_root(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[tail-boundary-batch] wrote {output_path}")
    print(
        "  "
        f"batches={summary['batch_count']} "
        f"mdl_tail_boundary_instances={summary['mdl_tail_boundary_instance_count']} "
        f"unique_families={summary['mdl_tail_boundary_families']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
