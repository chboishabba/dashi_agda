#!/usr/bin/env python3
"""Emit the fail-closed official periodic Navier--Stokes completion ledger."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

SCHEMA = "ns_official_completion_ledger.v1"


def digest(payload: Any) -> str:
    raw = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(raw).hexdigest()


def build() -> dict[str, Any]:
    stages = [
        {
            "id": "official_norm_identification",
            "module": "NSPeriodicOfficialNormIdentification.agda",
            "assembly": "machine_checked",
            "analytic_input": "conditional",
        },
        {
            "id": "near_triad_cutoff_uniform",
            "module": "NSPeriodicNearTriadCutoffUniformCompletion.agda",
            "assembly": "machine_checked",
            "analytic_input": "conditional",
        },
        {
            "id": "far_low_official_schur",
            "module": "NSPeriodicFarLowOfficialSchurCompletion.agda",
            "assembly": "machine_checked",
            "analytic_input": "conditional",
        },
        {
            "id": "far_high_official_tail",
            "module": "NSPeriodicFarHighTailCompletion.agda",
            "assembly": "machine_checked",
            "analytic_input": "conditional",
        },
        {
            "id": "wall_i_harmonic",
            "module": "NSPeriodicWallIHarmonicCompletion.agda",
            "assembly": "machine_checked",
            "analytic_input": "conditional",
        },
        {
            "id": "integrated_expenditure",
            "module": "NSPeriodicIntegratedExpenditureCompletion.agda",
            "assembly": "machine_checked",
            "analytic_input": "conjectural",
        },
        {
            "id": "normalized_boundary",
            "module": "NSCompactGammaNormalizedBoundaryInwardnessCompletion.agda",
            "assembly": "machine_checked",
            "analytic_input": "conjectural",
        },
        {
            "id": "switch_cost",
            "module": "NSPeriodicAdaptiveSwitchCostCompletion.agda",
            "assembly": "machine_checked",
            "analytic_input": "conjectural",
        },
        {
            "id": "diffuse_bkm",
            "module": "NSPeriodicDiffuseSpectrumBKMCompletion.agda",
            "assembly": "machine_checked",
            "analytic_input": "conjectural",
        },
        {
            "id": "all_data_coverage",
            "module": "NSPeriodicAllDataCoverageCompletion.agda",
            "assembly": "machine_checked",
            "analytic_input": "conjectural",
        },
        {
            "id": "cutoff_continuum_bkm",
            "module": "NSPeriodicCutoffUniformContinuumBKMCompletion.agda",
            "assembly": "machine_checked",
            "analytic_input": "conjectural",
        },
    ]
    payload: dict[str, Any] = {
        "schema": SCHEMA,
        "authority": "proof_relevant_reduction_and_fail_closed_status_only",
        "dependency_order": [stage["id"] for stage in stages],
        "stages": stages,
        "negative_findings_preserved": {
            "raw_multiplier_gain_is_full_far_low_bound": False,
            "static_compact_gamma_implies_adjacent_contraction": False,
            "absolute_packet_floor_is_invariant": False,
        },
        "promotion": {
            "official_harmonic_inputs_inhabited": False,
            "integrated_expenditure_inhabited": False,
            "normalized_adaptive_coverage_inhabited": False,
            "diffuse_and_switch_coverage_inhabited": False,
            "cutoff_uniform_continuum_completion_inhabited": False,
            "unconditional_periodic_navier_stokes": False,
            "clay_submission": False,
        },
    }
    payload["sha256"] = digest(payload)
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    payload = build()
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(payload, sort_keys=True, indent=2 if args.pretty else None) + "\n"
    args.output_json.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
