#!/usr/bin/env python3
"""Validate the deterministic seven-leaf periodic NS ledger."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

SCHEMA = "ns_seven_analytic_leaf_ledger.v1"
REQUIRED = [
    "official_carrier_uniform_harmonic",
    "compact_gamma_strict_expenditure",
    "strict_normalized_boundary_signs",
    "universal_switch_control",
    "diffuse_spectrum_bkm",
    "exhaustive_zero_chart_diffuse",
    "cutoff_uniform_bound_and_limit_transport",
]
REDUCTIONS = [
    "biot_savart_transversality",
    "strict_dissipation_margin",
    "strict_margin_expenditure_adapter",
    "packet_fraction_quotient_sign",
    "common_boundary_parameters",
    "hysteresis_separation",
    "adaptive_switch_separation_adapter",
    "diffuse_dissipation_charging",
    "diffuse_dissipation_route_adapter",
    "zero_chart_diffuse_selection",
    "extended_coverage_bkm",
    "weighted_envelope_limit_transport",
    "weighted_envelope_continuum_adapter",
]


def digest(payload: Any) -> str:
    raw = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(raw).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-json", type=Path, required=True)
    parser.add_argument("--output-json", type=Path, required=True)
    args = parser.parse_args()

    payload = json.loads(args.source_json.read_text(encoding="utf-8"))
    supplied = payload.pop("sha256", None)
    leaves = payload.get("leaves", [])
    leaf_map = {leaf.get("id"): leaf for leaf in leaves}
    reductions = payload.get("machine_checked_reductions", [])
    reduction_map = {entry.get("id"): entry for entry in reductions}
    coherence = payload.get("coherence", {})
    negatives = payload.get("negative_findings_preserved", {})
    promotion = payload.get("promotion", {})

    checks = {
        "schema": payload.get("schema") == SCHEMA,
        "digest": supplied == digest(payload),
        "dependency_order": payload.get("dependency_order") == REQUIRED,
        "all_leaves_present": all(name in leaf_map for name in REQUIRED),
        "all_completion_lists_nonempty": all(
            bool(leaf_map.get(name, {}).get("completion")) for name in REQUIRED
        ),
        "all_leaves_unpromoted": all(
            leaf_map.get(name, {}).get("status") in {"conditional", "conjectural"}
            for name in REQUIRED
        ),
        "all_reductions_present": all(name in reduction_map for name in REDUCTIONS),
        "all_reductions_machine_checked": all(
            reduction_map.get(name, {}).get("status") == "machine_checked_reduction"
            for name in REDUCTIONS
        ),
        "reductions_name_module_and_result": all(
            bool(reduction_map.get(name, {}).get("module"))
            and bool(reduction_map.get(name, {}).get("result"))
            for name in REDUCTIONS
        ),
        "carrier_coherence_required": bool(coherence)
        and all(value is True for value in coherence.values()),
        "negative_findings_preserved": bool(negatives)
        and all(value is False for value in negatives.values()),
        "all_promotions_false": bool(promotion)
        and all(value is False for value in promotion.values()),
    }
    errors = [name for name, ok in checks.items() if not ok]
    output = {
        "schema": "check_ns_seven_analytic_leaf_ledger.v1",
        "checks": checks,
        "errors": errors,
        "error_count": len(errors),
        "ok": not errors,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(
        json.dumps(output, sort_keys=True, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(output, sort_keys=True, indent=2))
    if errors:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
