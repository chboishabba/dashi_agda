#!/usr/bin/env python3
from __future__ import annotations

import json
from pathlib import Path

from iit4_finite_reference import (
    IIT4_2023,
    IIT4_2026,
    deterministic_model,
    feedforward_three_cell_step,
    recurrent_three_cell_step,
    system_phi,
)


def xor2(a: int, b: int) -> int:
    return a ^ b


def tri_xor(a: int, b: int) -> int:
    return (a + b) % 3


def grid_step(state: tuple[int, ...]) -> tuple[int, ...]:
    nw, ne, sw, se = state
    return (ne ^ sw, nw ^ se, nw ^ se, ne ^ sw)


def _scan(model) -> dict:
    out = {}
    for formalism in (IIT4_2023, IIT4_2026):
        receipts = [system_phi(model, state, formalism=formalism) for state in model.states]
        values = [receipt["phi_s"] for receipt in receipts]
        out[formalism.lower()] = {
            "states_tested": len(receipts),
            "zero_phi_states": sum(abs(value) < 1.0e-12 for value in values),
            "distinct_phi_s": sorted({round(value, 12) for value in values}),
        }
    return out


def fixture_summary() -> dict:
    fixtures = {
        "open_xor_path": deterministic_model(
            2, 3, feedforward_three_cell_step(xor2), label="open XOR causal path"
        ),
        "closed_xor_cycle": deterministic_model(
            2, 3, recurrent_three_cell_step(xor2), label="closed XOR causal cycle"
        ),
        "xor_grid_2x2": deterministic_model(2, 4, grid_step, label="2x2 XOR fabric"),
        "closed_trixor_cycle": deterministic_model(
            3, 3, recurrent_three_cell_step(tri_xor), label="closed triXor causal cycle"
        ),
    }
    return {
        "contract": "iit_hyperfabric_fixture_scan",
        "fixtures": {name: _scan(model) for name, model in fixtures.items()},
        "partition_semantics": [
            "causal_graph_connection_partition",
            "stalk_restriction_partition",
            "global_section_partition",
        ],
        "boundary": {
            "these_partition_semantics_are_definitionally_identical": False,
            "pants_seam_rewrites_hyperfabric_incidence_automatically": False,
            "numeric_scan_currently_evaluates_causal_graph_partition_only": True,
            "global_section_semantics_require_existing_compatibility_witness": True,
        },
    }


def main() -> None:
    summary = fixture_summary()
    output = Path(__file__).with_name("data") / "outputs" / "iit_hyperfabric_fixture_scan.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
