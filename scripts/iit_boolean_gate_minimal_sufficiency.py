#!/usr/bin/env python3
"""Exhaust the 16 Boolean laws on the fixed recurrent IIT fixture.

Numerical scope only.  Formal truth-table/bipermutativity classification is
owned by IITBooleanParityMinimalSufficiencyExact.agda.
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


def left_permutative(bits: tuple[int, int, int, int]) -> bool:
    gate = gate_from_bits(bits)
    return all(gate(0, b) != gate(1, b) for b in (0, 1))


def right_permutative(bits: tuple[int, int, int, int]) -> bool:
    gate = gate_from_bits(bits)
    return all(gate(a, 0) != gate(a, 1) for a in (0, 1))


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
            2, 3, recurrent_three_cell_step(gate),
            label="bool-" + "".join(map(str, bits)),
        )
        values = [
            system_phi(model, state, formalism=IIT4_2023)["phi_s"]
            for state in model.states
        ]
        lp = left_permutative(bits)
        rp = right_permutative(bits)
        rows.append({
            "truth_table_00_01_10_11": "".join(map(str, bits)),
            "label": label(bits),
            "balanced": balanced(bits),
            "depends_on_left": depends_on_left(bits),
            "depends_on_right": depends_on_right(bits),
            "essential_two_input": depends_on_left(bits) and depends_on_right(bits),
            "left_permutative": lp,
            "right_permutative": rp,
            "bipermutative": lp and rp,
            "distinct_phi_s_2023": sorted({round(v, 12) for v in values}),
            "zero_phi_states": sum(abs(v) < 1.0e-12 for v in values),
            "positive_all_states": all(v > 1.0e-12 for v in values),
        })

    essential_uniform = [r for r in rows if r["essential_two_input"] and r["positive_all_states"]]
    bipermutative = [r for r in rows if r["bipermutative"]]
    essential_balanced = [r for r in rows if r["essential_two_input"] and r["balanced"]]

    expected = {"XOR", "XNOR"}
    assert {r["label"] for r in essential_uniform} == expected
    assert {r["label"] for r in bipermutative} == expected
    assert {r["label"] for r in essential_balanced} == expected

    return {
        "contract": "boolean_gate_minimal_sufficiency_numeric",
        "formalism": IIT4_2023,
        "fabric": "A'=C; B'=A; C'=mu(A,B)",
        "gate_count": 16,
        "rows": rows,
        "bipermutative_class": [r["label"] for r in bipermutative],
        "essential_two_input_positive_all_states": [r["label"] for r in essential_uniform],
        "essential_balanced_class": [r["label"] for r in essential_balanced],
        "conclusion": (
            "XOR/XNOR are exactly the bipermutative Boolean laws and exactly the "
            "genuinely two-input laws with positive 2023 system-phi in every state "
            "on this recurrent fabric."
        ),
        "boundary": {
            "numeric_receipt_is_agda_proof": False,
            "bipermutativity_is_full_iit_big_phi": False,
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
