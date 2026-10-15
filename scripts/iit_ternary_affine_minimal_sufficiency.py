#!/usr/bin/env python3
"""Numerically scan all 27 affine F3 two-input laws on the recurrent fixture.

Laws have the form mu(a,b)=c+alpha*a+beta*b mod 3.  The scan shows that every
genuinely two-input affine law (alpha,beta != 0) has the same all-state-positive
2023 system-phi profile log2(9).  In particular both symmetric triXor a+b and
antisymmetric difference a-b are sufficient on the selected fabric.
"""
from __future__ import annotations

import json
from itertools import product
from pathlib import Path

from iit4_finite_reference import IIT4_2023, deterministic_model, recurrent_three_cell_step, system_phi


def scan() -> dict:
    rows = []
    for c, alpha, beta in product(range(3), repeat=3):
        def gate(a: int, b: int, c=c, alpha=alpha, beta=beta) -> int:
            return (c + alpha * a + beta * b) % 3
        model = deterministic_model(3, 3, recurrent_three_cell_step(gate), label=f"affine-{c}-{alpha}-{beta}")
        values = [system_phi(model, state, formalism=IIT4_2023)["phi_s"] for state in model.states]
        rows.append({
            "c": c,
            "alpha": alpha,
            "beta": beta,
            "essential_two_input": alpha != 0 and beta != 0,
            "distinct_phi_s_2023": sorted({round(v, 12) for v in values}),
            "zero_phi_states": sum(abs(v) < 1.0e-12 for v in values),
            "positive_all_states": all(v > 1.0e-12 for v in values),
            "swap_antisymmetric_linear_part": (alpha + beta) % 3 == 0 and alpha != 0,
        })
    essential = [r for r in rows if r["essential_two_input"]]
    assert len(essential) == 12
    assert all(r["distinct_phi_s_2023"] == [3.169925001442] for r in essential)
    assert all(r["positive_all_states"] for r in essential)
    antisymmetric = [r for r in essential if r["swap_antisymmetric_linear_part"]]
    assert len(antisymmetric) == 6
    return {
        "contract": "ternary_affine_minimal_sufficiency_numeric",
        "formalism": IIT4_2023,
        "fabric": "A'=C; B'=A; C'=c+alpha*A+beta*B mod 3",
        "affine_gate_count": 27,
        "essential_two_input_count": len(essential),
        "essential_all_state_phi_s": [3.169925001442],
        "antisymmetric_affine_count": len(antisymmetric),
        "sum_gate": {"c": 0, "alpha": 1, "beta": 1},
        "difference_gate": {"c": 0, "alpha": 1, "beta": 2},
        "rows": rows,
        "boundary": {
            "numeric_receipt_is_agda_proof": False,
            "antisymmetric_difference_is_physical_torque": False,
            "2026_deterministic_phi_claimed_positive": False,
        },
    }


def main() -> None:
    receipt = scan()
    output = Path(__file__).with_name("data") / "outputs" / "iit_ternary_affine_minimal_sufficiency.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
