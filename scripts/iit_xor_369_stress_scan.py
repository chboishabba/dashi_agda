#!/usr/bin/env python3
from __future__ import annotations

import json
from pathlib import Path

from iit_369_algebra_scan import algebra_summary
from iit_matched_fabric_gate_sweep import sweep_summary


def stress_summary() -> dict:
    matched = sweep_summary()
    algebra = algebra_summary()
    fixed = matched["fixed_recurrent_fabric_vary_gate"]
    topology = matched["fixed_binary_xor_vary_fabric"]
    return {
        "binary_recurrent_xor": fixed["binary_xor"],
        "binary_xor_grid_2x2": topology["grid_2x2"],
        "ternary_recurrent_trixor": fixed["ternary_trixor"],
        "z6_recurrent_addition": algebra["z6_cyclic"],
        "s3_recurrent_composition": algebra["s3_permutation"],
        "z9_recurrent_addition": algebra["z9_cyclic"],
        "f3_squared_recurrent_addition": algebra["f3_squared"],
        "boundary": {
            "system_phi_ranking_is_consciousness_ranking": False,
            "historical_iit_counterexample_equals_iit4_big_phi": False,
            "different_alphabet_sizes_directly_rankable_without_normalization_analysis": False,
            "deterministic_2026_system_phi_collapses_these_fixtures_to_zero": True,
            "cause_effect_structure_may_still_be_analyzed_when_2026_phi_s_is_zero": True,
        },
    }


def main() -> None:
    summary = stress_summary()
    output = Path(__file__).with_name("data") / "outputs" / "iit_xor_369_stress_scan.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
