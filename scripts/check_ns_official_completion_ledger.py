#!/usr/bin/env python3
"""Validate the deterministic official NS completion ledger."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

SCHEMA = "ns_official_completion_ledger.v1"
REQUIRED = [
    "official_norm_identification",
    "near_triad_cutoff_uniform",
    "far_low_official_schur",
    "far_high_official_tail",
    "wall_i_harmonic",
    "integrated_expenditure",
    "normalized_boundary",
    "switch_cost",
    "diffuse_bkm",
    "all_data_coverage",
    "all_data_cutoff_coverage",
    "cutoff_continuum_bkm",
]
REUSED = [
    "concrete_bernstein_be1_be8",
    "published_periodic_harmonic_authority",
    "factorized_official_far_low_schur",
    "concrete_real_integration",
    "galerkin_g1_g19_continuum",
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
    stages = payload.get("stages", [])
    stage_map = {stage.get("id"): stage for stage in stages}
    reused = payload.get("reused_repository_lanes", [])
    reused_map = {lane.get("id"): lane for lane in reused}
    promotion = payload.get("promotion", {})
    negatives = payload.get("negative_findings_preserved", {})

    checks = {
        "schema": payload.get("schema") == SCHEMA,
        "authority": payload.get("authority")
        == "proof_relevant_reduction_and_fail_closed_status_only",
        "digest": supplied == digest(payload),
        "dependency_order": payload.get("dependency_order") == REQUIRED,
        "all_stages_present": all(stage in stage_map for stage in REQUIRED),
        "assemblies_machine_checked": all(
            stage_map.get(stage, {}).get("assembly") == "machine_checked"
            for stage in REQUIRED
        ),
        "analytic_inputs_not_promoted": all(
            stage_map.get(stage, {}).get("analytic_input")
            in {"conditional", "conjectural"}
            for stage in REQUIRED
        ),
        "all_reused_lanes_present": all(lane in reused_map for lane in REUSED),
        "reused_lanes_are_machine_checked_adapters": all(
            reused_map.get(lane, {}).get("status") == "machine_checked_adapter"
            for lane in REUSED
        ),
        "reused_lanes_name_source_and_adapter": all(
            bool(reused_map.get(lane, {}).get("source"))
            and bool(reused_map.get(lane, {}).get("adapter"))
            for lane in REUSED
        ),
        "all_promotions_false": bool(promotion)
        and all(value is False for value in promotion.values()),
        "negative_findings_preserved": bool(negatives)
        and all(value is False for value in negatives.values()),
    }
    errors = [name for name, ok in checks.items() if not ok]
    out = {
        "schema": "check_ns_official_completion_ledger.v1",
        "checks": checks,
        "error_count": len(errors),
        "errors": errors,
        "ok": not errors,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(
        json.dumps(out, sort_keys=True, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(out, sort_keys=True, indent=2))
    if errors:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
