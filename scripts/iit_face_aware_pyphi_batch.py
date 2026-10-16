#!/usr/bin/env python3
"""Run the matched face-aware causal pair through the pinned PyPhi oracle.

This script is intentionally thin.  It generates PyPhi state-by-node TPMs in
PyPhi's little-endian binary row ordering, runs every current state of both
models through the existing ``iit4_pyphi_oracle`` adapter, and writes one batch
JSON receipt.

If PyPhi is unavailable the script fails closed through the existing oracle;
it never substitutes DASHI's system-phi reference or stored calibration values
for distinctions, relations, or big-Phi.
"""
from __future__ import annotations

import argparse
import json
import tempfile
from itertools import product
from pathlib import Path

from iit4_pyphi_oracle import json_fixture_receipt
from iit_face_aware_triadic_experiment import pairwise_step, triadic_step


def little_endian_states(unit_count: int):
    for index in range(2**unit_count):
        yield tuple((index >> bit) & 1 for bit in range(unit_count))


def state_by_node_tpm(step, unit_count: int = 3):
    return [list(step(state)) for state in little_endian_states(unit_count)]


def fixture(label: str, step, state):
    return {
        "formalism": "IIT_4_0_2023",
        "label": label,
        "node_labels": ["A", "B", "C"],
        "tpm_row_order": "little_endian_state_index",
        "tpm": state_by_node_tpm(step),
        "state": list(state),
        "subset": [0, 1, 2],
    }


def run_fixture(payload: dict) -> dict:
    with tempfile.TemporaryDirectory(prefix="iit-face-aware-") as td:
        path = Path(td) / "fixture.json"
        path.write_text(json.dumps(payload))
        receipt = json_fixture_receipt(path)
    receipt["fixture_label"] = payload["label"]
    receipt["current_state"] = payload["state"]
    receipt["tpm_row_order"] = payload["tpm_row_order"]
    return receipt


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    analyses = []
    for label, step in (
        ("pairwise-face-model", pairwise_step),
        ("triadic-face-model", triadic_step),
    ):
        for state in product(range(2), repeat=3):
            analyses.append(run_fixture(fixture(label, step, state)))

    by_state = {}
    for row in analyses:
        key = "".join(map(str, row["current_state"]))
        by_state.setdefault(key, {})[row["fixture_label"]] = row

    receipt = {
        "contract": "iit_face_aware_full_ces_batch",
        "formalism": "IIT_4_0_2023",
        "model_relation": (
            "The two TPMs agree on all coordinate faces and differ by the pure "
            "three-way ABC term at the interior state 111."
        ),
        "analyses": analyses,
        "paired_by_state": by_state,
        "boundary": (
            "This is an external PyPhi numerical receipt. Agda owns the exact "
            "same-face/different-interior theorem; PyPhi owns numerical CES unfolding."
        ),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(args.output)


if __name__ == "__main__":
    main()
