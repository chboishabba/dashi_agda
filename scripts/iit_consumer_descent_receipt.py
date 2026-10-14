#!/usr/bin/env python3
from __future__ import annotations

import json
from pathlib import Path

from iit_369_algebra_scan import algebra_summary


def consumer_descent_summary() -> dict:
    algebra = algebra_summary()
    same_profile = algebra["comparison"]["same_2023_system_phi_profile"]
    return {
        "contract": "iit_consumer_descent_receipt",
        "exact_kernel_witnesses": {
            "nine_state_cardinality_loses_group_law": True,
            "three_selected_cubies_lose_triadic_face": True,
        },
        "numeric_witnesses": {
            "matched_z9_f3_squared_same_2023_phi_profile": same_profile,
            "matched_z9_f3_squared_consumer_differs": True,
            "system_phi_profile_fails_group_law_consumer_on_tested_fixture": (
                same_profile and algebra["comparison"]["same_group_law"] is False
            ),
        },
        "observation_levels": [
            "system_phi_s_only",
            "distinctions_only",
            "full_cause_effect_structure",
        ],
        "boundary": {
            "numeric_collision_is_agda_kernel_proof": False,
            "high_phi_implies_phenomenal_identity": False,
            "one_observer_is_sufficient_for_every_consumer": False,
            "consumer_factorization_must_be_paid_per_consumer": True,
        },
    }


def main() -> None:
    summary = consumer_descent_summary()
    output = Path(__file__).with_name("data") / "outputs" / "iit_consumer_descent_receipt.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
