#!/usr/bin/env python3
from __future__ import annotations

import importlib
import json
from pathlib import Path

CHECKS = (
    ("iit4_finite_reference", "check_iit4_finite_reference"),
    ("xor_grid_calibration", "check_iit_xor_grid_calibration"),
    ("matched_fabric_gate", "check_iit_matched_fabric_gate_sweep"),
    ("algebra_369", "check_iit_369_algebra_scan"),
    ("hyperfabric_fixtures", "check_iit_hyperfabric_fixture_scan"),
    ("pointed27_gluing", "check_iit_pointed27_gluing_scan"),
    ("structure_arithmetic", "check_iit4_structure_reference"),
    ("xor_369_stress", "check_iit_xor_369_stress_scan"),
)


def main() -> None:
    statuses = {}
    for label, module_name in CHECKS:
        module = importlib.import_module(module_name)
        module.main()
        statuses[label] = "PASS"

    # Consumer-descent receipt is data-producing rather than assert-only.
    consumer = importlib.import_module("iit_consumer_descent_receipt")
    summary = consumer.consumer_descent_summary()
    assert summary["exact_kernel_witnesses"]["nine_state_cardinality_loses_group_law"]
    assert summary["numeric_witnesses"]["system_phi_profile_fails_group_law_consumer_on_tested_fixture"]
    statuses["consumer_descent"] = "PASS"

    receipt = {
        "contract": "iit_hyperfabric_completion",
        "python_checks": statuses,
        "pyphi_full_structure_oracle": "ADAPTER_PRESENT_NOT_REQUIRED_FOR_LOCAL_CHECKS",
        "agda_kernel": "PENDING_EXTERNAL_AGDA_OR_CI_RECEIPT",
        "source_complete_tasks": list(range(1, 11)),
    }
    output = Path(__file__).with_name("data") / "outputs" / "iit_hyperfabric_completion.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
