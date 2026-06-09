#!/usr/bin/env python3
from __future__ import annotations

import argparse
import ast
import hashlib
import importlib.util
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


DEFAULT_DASHIQ_ROOT = Path("/home/c/Documents/code/dashiQ")
SCHEMA = "dashi-sm-higgs-hepdata-receipt-v1"
SCHEMA_VERSION = "1.0.0"


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def read_ast(path: Path) -> ast.Module:
    return ast.parse(path.read_text(encoding="utf-8"), filename=str(path))


def literal_assignment(tree: ast.Module, name: str) -> Any:
    for node in tree.body:
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name) and target.id == name:
                    return ast.literal_eval(node.value)
    raise ValueError(f"{name} not found as a literal assignment")


def parser_choices_for_argument(tree: ast.Module, option_name: str) -> list[str]:
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        if not isinstance(node.func, ast.Attribute) or node.func.attr != "add_argument":
            continue
        if not node.args:
            continue
        first = node.args[0]
        if not isinstance(first, ast.Constant) or first.value != option_name:
            continue
        for keyword in node.keywords:
            if keyword.arg == "choices":
                return [str(item) for item in ast.literal_eval(keyword.value)]
    raise ValueError(f"{option_name} choices not found")


def source_descriptor(path: Path, role: str) -> dict[str, Any]:
    return {
        "path": str(path),
        "role": role,
        "size_bytes": path.stat().st_size,
        "sha256": sha256_file(path),
    }


def load_python_module(path: Path, module_name: str) -> Any:
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load module spec for {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def best_model_row(table_name: str, basis: str, results: list[tuple[float, float]]) -> dict[str, Any]:
    labels = ["A", "B", "C"]
    rows = [
        {"model": label, "chi2": float(chi2), "mdl": float(mdl)}
        for label, (chi2, mdl) in zip(labels, results)
    ]
    sorted_rows = sorted(rows, key=lambda row: row["mdl"])
    return {
        "observable": table_name,
        "basis": basis,
        "models": rows,
        "best_model": sorted_rows[0]["model"],
        "mdl_margin_to_second": float(sorted_rows[1]["mdl"] - sorted_rows[0]["mdl"]),
    }


def run_observed_shape_analysis(script_path: Path, observables: list[tuple[str, str, str]]) -> list[dict[str, Any]]:
    module = load_python_module(script_path, "dashiq_13tev_receipt_source")
    rows = []
    for table_name, corr_table_name, basis in observables:
        try:
            results = module.run_one(table_name, corr_table_name, basis)
        except Exception as exc:  # pragma: no cover - network/provider path
            rows.append(
                {
                    "observable": table_name,
                    "basis": basis,
                    "status": "provider-run-failed",
                    "error": str(exc),
                }
            )
            continue
        row = best_model_row(table_name, basis, list(results))
        row["status"] = "ok"
        row["correlation_table"] = corr_table_name
        rows.append(row)
    return rows


def build_receipts(
    dashiq_root: Path,
    *,
    generated_at: str,
    run_observed: bool,
) -> dict[str, Any]:
    thirteen_tev = dashiq_root / "13tev.py"
    pseudo_harness = dashiq_root / "pseudo_data_harness.py"
    reusable_query = dashiq_root / "reusable_query.py"
    resolver = dashiq_root / "resolve_hepdata_record.py"

    required = [thirteen_tev, pseudo_harness, reusable_query, resolver]
    missing = [str(path) for path in required if not path.exists()]
    if missing:
        raise FileNotFoundError("missing required dashiQ sources: " + ", ".join(missing))

    observed_tree = read_ast(thirteen_tev)
    pseudo_tree = read_ast(pseudo_harness)
    observed_record = str(literal_assignment(observed_tree, "HEPDATA_RECORD"))
    observed_observables = literal_assignment(observed_tree, "OBSERVABLES")
    pseudo_record = str(literal_assignment(pseudo_tree, "HEPDATA_RECORD"))
    pseudo_observables = literal_assignment(pseudo_tree, "OBSERVABLES")
    injection_modes = parser_choices_for_argument(pseudo_tree, "--inject")
    projections = parser_choices_for_argument(pseudo_tree, "--projection")

    live_rows: list[dict[str, Any]] = []
    if run_observed:
        live_rows = run_observed_shape_analysis(thirteen_tev, observed_observables)

    source_files = [
        source_descriptor(thirteen_tev, "observed full-covariance MDL shape-complexity analysis"),
        source_descriptor(pseudo_harness, "pseudo-data detectability harness using published covariance"),
        source_descriptor(reusable_query, "HEPData query helper"),
        source_descriptor(resolver, "HEPData record resolver"),
    ]

    observed_receipt = {
        "schema": SCHEMA,
        "schema_version": SCHEMA_VERSION,
        "receipt_kind": "observed-shape-complexity",
        "generated_at_utc": generated_at,
        "authority_provider": "HEPData",
        "experiment_authority": "ATLAS",
        "hepdata_record": observed_record,
        "hepdata_record_url": f"https://www.hepdata.net/record/{observed_record}",
        "observable_count": len(observed_observables),
        "observables": [
            {
                "table": table,
                "correlation_table": corr,
                "basis": basis,
                "covariance_required": True,
            }
            for table, corr, basis in observed_observables
        ],
        "analysis_mode": "Path C shape-complexity over flat y_ref",
        "model_family": ["A normalization", "B tilt", "C curvature"],
        "full_covariance_surface_present": True,
        "sm_relative_baseline_present": False,
        "accepted_authority_token_present": False,
        "empirical_validation_promoted": False,
        "source_files": source_files,
        "live_observed_results": live_rows,
    }

    pseudo_receipt = {
        "schema": SCHEMA,
        "schema_version": SCHEMA_VERSION,
        "receipt_kind": "pseudo-detectability",
        "generated_at_utc": generated_at,
        "authority_provider": "HEPData",
        "experiment_authority": "ATLAS",
        "hepdata_record": pseudo_record,
        "hepdata_record_url": f"https://www.hepdata.net/record/{pseudo_record}",
        "observable_count": len(pseudo_observables),
        "observables": [
            {
                "table": table,
                "correlation_table": corr,
                "basis": basis,
                "covariance_required": True,
            }
            for table, corr, basis in pseudo_observables
        ],
        "injection_modes": injection_modes,
        "projection_modes": projections,
        "detectability_contract": "selection-rate calibration for controlled pseudo-data injections",
        "full_covariance_surface_present": True,
        "observed_new_physics_claim": False,
        "accepted_authority_token_present": False,
        "empirical_validation_promoted": False,
        "source_files": source_files,
    }

    summary = {
        "schema": SCHEMA,
        "schema_version": SCHEMA_VERSION,
        "receipt_kind": "adapter-summary",
        "generated_at_utc": generated_at,
        "source_root": str(dashiq_root),
        "source_file_count": len(source_files),
        "receipt_files": [
            "sm_higgs_observed_shape_receipt.json",
            "sm_higgs_pseudo_detectability_receipt.json",
            "sm_higgs_adapter_summary.json",
        ],
        "gates": {
            "source_checksums_bound": True,
            "full_covariance_surface_present": True,
            "pseudo_detectability_surface_present": True,
            "sm_relative_baseline_present": False,
            "accepted_authority_token_present": False,
            "holdout_protocol_accepted": False,
            "empirical_validation_promoted": False,
            "standard_model_promoted": False,
        },
        "next_required_receipts": [
            "SM-relative theory baseline table or generator replay digest",
            "HEPData/provider source checksum and version token accepted by repo authority policy",
            "covariance comparison law with predeclared pass/fail criterion",
            "holdout or frozen-prediction protocol separating discovery from validation",
        ],
        "observed_shape_receipt": "sm_higgs_observed_shape_receipt.json",
        "pseudo_detectability_receipt": "sm_higgs_pseudo_detectability_receipt.json",
    }

    return {
        "observed": observed_receipt,
        "pseudo": pseudo_receipt,
        "summary": summary,
    }


def write_receipts(receipts: dict[str, Any], output_dir: Path) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)
    mapping = {
        "observed": "sm_higgs_observed_shape_receipt.json",
        "pseudo": "sm_higgs_pseudo_detectability_receipt.json",
        "summary": "sm_higgs_adapter_summary.json",
    }
    for key, filename in mapping.items():
        (output_dir / filename).write_text(
            json.dumps(receipts[key], indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

    gates = receipts["summary"]["gates"]
    lines = [
        "# SM Higgs HEPData Receipt Adapter",
        "",
        f"- schema: `{SCHEMA}`",
        f"- source root: `{receipts['summary']['source_root']}`",
        f"- source files: `{receipts['summary']['source_file_count']}`",
        f"- full covariance surface present: `{str(gates['full_covariance_surface_present']).lower()}`",
        f"- pseudo detectability surface present: `{str(gates['pseudo_detectability_surface_present']).lower()}`",
        f"- SM-relative baseline present: `{str(gates['sm_relative_baseline_present']).lower()}`",
        f"- accepted authority token present: `{str(gates['accepted_authority_token_present']).lower()}`",
        f"- empirical validation promoted: `{str(gates['empirical_validation_promoted']).lower()}`",
        "",
        "## Next Required Receipts",
        "",
    ]
    lines.extend(f"- {item}" for item in receipts["summary"]["next_required_receipts"])
    (output_dir / "sm_higgs_hepdata_receipt_adapter.md").write_text(
        "\n".join(lines) + "\n",
        encoding="utf-8",
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Emit checksum-bound DASHI receipts from dashiQ Higgs/HEPData surfaces."
    )
    parser.add_argument("--dashiq-root", type=Path, default=DEFAULT_DASHIQ_ROOT)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("outputs/sm_higgs_hepdata_receipts"),
    )
    parser.add_argument(
        "--generated-at",
        default=None,
        help="Fixed timestamp for reproducible tests. Defaults to current UTC.",
    )
    parser.add_argument(
        "--run-observed",
        action="store_true",
        help="Also run the live HEPData observed-shape fits and embed the resulting MDL rows.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    generated_at = args.generated_at or datetime.now(timezone.utc).isoformat()
    receipts = build_receipts(
        args.dashiq_root,
        generated_at=generated_at,
        run_observed=args.run_observed,
    )
    write_receipts(receipts, args.output_dir)
    print(json.dumps(receipts["summary"], indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
