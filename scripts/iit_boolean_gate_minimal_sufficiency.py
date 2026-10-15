#!/usr/bin/env python3
"""Exhaust the 16 two-input Boolean synthesis laws on one recurrent fabric.

Numerical scope only.  Formal truth-table classification is owned by
DASHI/Biology/IITBooleanParityMinimalSufficiencyExact.agda.

Fabric:
    A[t+1] = C[t]
    B[t+1] = A[t]
    C[t+1] = mu(A[t], B[t])

For every Boolean truth table mu, compute the 2023 IIT-4 system-phi profile over
all eight system states.  Then identify the genuinely two-input laws (both
inputs essential) whose phi is positive for every state.
"""
from __future__ import annotations

import json
from itertools import product
from pathlib import Path

from iit4_finite_reference import (
    IIT4_2023,
    deterministic_model,
    recurrent_three_cell_step,
    system_phi,
)


def gate_from_bits(bits: tuple[int, int, int, int]):
    def gate(a: int, b: int) -> int:
        return bits[2 * a + b]
    return gate


def depends_on_left(bits: tuple[int, int, int, int]) -> bool:
    gate = gate_from_bits(bits)
    return any(gate(0, b) != gate(1, b) for b in (0, 1))


def depends_on_right(bits: tuple[int, int, int, int]) -> bool:
    gate = gate_from_bits(bits)
    return any(gate(a, 0) != gate(a, 1) for a in (0, 1))


def balanced(bits: tuple[int, int, int, int]) -> bool:
    return sum(bits) == 2


def label(bits: tuple[int, int, int, int]) -> str:
    known = {
        (0, 0, 0, 0): "FALSE",
        (0, 0, 0, 1): "AND",
        (0, 1, 1, 0): "XOR",
        (0, 1, 1, 1): "OR",
        (1, 0, 0, 0): "NOR",
        (1, 0, 0, 1): "XNOR",
        (1, 1, 1, 0): "NAND",
        (1, 1, 1, 1): "TRUE",
        (0, 0, 1, 1): "A",
        (1, 1, 0, 0): "NOT_A",
        (0, 1, 0, 1): "B",
        (1, 0, 1, 0): "NOT_B",
    }
    return known.get(bits, "gate_" + "".join(map(str, bits)))


def scan() -> dict:
    rows = []
    for bits in product((0, 1), repeat=4):
        gate = gate_from_bits(bits)
        model = deterministic_model(
            2,
            3,
            recurrent_three_cell_step(gate),
            label="bool-" + "".join(map(str, bits)),
        )
        values = [
            system_phi(model, state, formalism=IIT4_2023)["phi_s"]
            for state in model.states
        ]
        row = {
            "truth_table_00_01_10_11": "".join(map(str, bits)),
            "label": label(bits),
            "balanced": balanced(bits),
            "depends_on_left": depends_on_left(bits),
            "depends_on_right": depends_on_right(bits),
            "essential_two_input": depends_on_left(bits) and depends_on_right(bits),
            "distinct_phi_s_2023": sorted({round(v, 12) for v in values}),
            "zero_phi_states": sum(abs(v) < 1.0e-12 for v in values),
            "positive_all_states": all(v > 1.0e-12 for v in values),
        }
        rows.append(row)

    essential_uniform = [
        row for row in rows
        if row["essential_two_input"] and row["positive_all_states"]
    ]
    essential_balanced = [
        row for row in rows
        if row["essential_two_input"] and row["balanced"]
    ]

    assert {row["label"] for row in essential_uniform} == {"XOR", "XNOR"}
    assert {row["label"] for row in essential_balanced} == {"XOR", "XNOR"}

    return {
        "contract": "boolean_gate_minimal_sufficiency_numeric",
        "formalism": IIT4_2023,
        "fabric": "A'=C; B'=A; C'=mu(A,B)",
        "gate_count": 16,
        "rows": rows,
        "essential_two_input_positive_all_states": [row["label"] for row in essential_uniform],
        "essential_balanced_class": [row["label"] for row in essential_balanced],
        "conclusion": (
            "On this recurrent fabric, XOR/XNOR are exactly the genuinely two-input "
            "Boolean laws with positive 2023 system-phi in every system state."
        ),
        "boundary": {
            "numeric_receipt_is_agda_proof": False,
            "xor_alone_encodes_input_order_or_torque": False,
            "current_2026_deterministic_phi_claimed_positive": False,
        },
    }


def main() -> None:
    receipt = scan()
    output = Path(__file__).with_name("data") / "outputs" / "iit_boolean_gate_minimal_sufficiency.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
