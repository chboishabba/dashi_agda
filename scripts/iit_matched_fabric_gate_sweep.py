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


def or2(a: int, b: int) -> int:
    return int(bool(a) or bool(b))


def and2(a: int, b: int) -> int:
    return int(bool(a) and bool(b))


def tri_xor(a: int, b: int) -> int:
    return (a + b) % 3


def grid_step(gate):
    def step(state: tuple[int, ...]) -> tuple[int, ...]:
        north_west, north_east, south_west, south_east = state
        return (
            gate(north_east, south_west),
            gate(north_west, south_east),
            gate(north_west, south_east),
            gate(north_east, south_west),
        )

    return step


def _scan(model) -> dict:
    result = {}
    for formalism in (IIT4_2023, IIT4_2026):
        receipts = [system_phi(model, state, formalism=formalism) for state in model.states]
        values = [receipt["phi_s"] for receipt in receipts]
        result[formalism.lower()] = {
            "states_tested": len(receipts),
            "zero_phi_states": sum(abs(value) < 1.0e-12 for value in values),
            "distinct_phi_s": sorted({round(value, 12) for value in values}),
            "distinct_mips": len(
                {
                    json.dumps(receipt["mip"], sort_keys=True)
                    for receipt in receipts
                    if receipt["mip"] is not None
                }
            ),
        }
    return result


def sweep_summary() -> dict:
    recurrent = {
        "binary_xor": deterministic_model(
            2, 3, recurrent_three_cell_step(xor2), label="recurrent-binary-xor"
        ),
        "binary_or": deterministic_model(
            2, 3, recurrent_three_cell_step(or2), label="recurrent-binary-or"
        ),
        "binary_and": deterministic_model(
            2, 3, recurrent_three_cell_step(and2), label="recurrent-binary-and"
        ),
        "ternary_trixor": deterministic_model(
            3, 3, recurrent_three_cell_step(tri_xor), label="recurrent-ternary-trixor"
        ),
    }

    binary_fabrics = {
        "feedforward": deterministic_model(
            2, 3, feedforward_three_cell_step(xor2), label="feedforward-binary-xor"
        ),
        "recurrent_three_cell": recurrent["binary_xor"],
        "grid_2x2": deterministic_model(
            2, 4, grid_step(xor2), label="grid2x2-binary-xor"
        ),
    }

    return {
        "contract": "iit_matched_fabric_gate_sweep",
        "fixed_recurrent_fabric_vary_gate": {
            name: _scan(model) for name, model in recurrent.items()
        },
        "fixed_binary_xor_vary_fabric": {
            name: _scan(model) for name, model in binary_fabrics.items()
        },
        "boundary": {
            "fabric_alone_determines_phi_s": False,
            "gate_alone_determines_phi_s": False,
            "current_state_can_change_phi_s": True,
            "2023_and_2026_system_phi_are_interchangeable": False,
        },
    }


def main() -> None:
    summary = sweep_summary()
    output = Path(__file__).with_name("data") / "outputs" / "iit_matched_fabric_gate_sweep.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
