#!/usr/bin/env python3
"""Numerical IIT experiment for a pure higher-order causal difference.

The two deterministic 3-bit transition laws agree whenever any one source bit
is zero; they differ only at 111 through the cubic A*B*C term.  This script is
numeric evidence only.  Agda owns the exact face-agreement/different-interior
statement in IITFaceAwareTriadicCausalPairExact.agda.
"""
from __future__ import annotations

import json
from itertools import product

from iit4_finite_reference import IIT4_2023, deterministic_model, system_phi


def xor(a: int, b: int) -> int:
    return a ^ b


def pairwise_step(state: tuple[int, ...]) -> tuple[int, ...]:
    a, b, c = state
    return xor(b, c), xor(a, c), xor(a, b)


def triadic_step(state: tuple[int, ...]) -> tuple[int, ...]:
    a, b, c = state
    abc = a & b & c
    return xor(b, c), xor(a, c), xor(xor(a, b), abc)


def scan(label: str, step):
    model = deterministic_model(2, 3, step, label=label)
    rows = []
    for state in product(range(2), repeat=3):
        receipt = system_phi(model, state, formalism=IIT4_2023)
        rows.append({"state": list(state), "phi_s": receipt["phi_s"]})
    return rows


def main() -> None:
    face_agreement = all(
        pairwise_step(state) == triadic_step(state)
        for state in product(range(2), repeat=3)
        if 0 in state
    )
    interior_difference = pairwise_step((1, 1, 1)) != triadic_step((1, 1, 1))

    receipt = {
        "formalism": IIT4_2023,
        "face_agreement": face_agreement,
        "interior_difference": interior_difference,
        "pairwise": scan("pairwise-face-model", pairwise_step),
        "triadic": scan("triadic-face-model", triadic_step),
        "boundary": (
            "This is system-phi_s numerical evidence, not a full distinction/"
            "relation/big-Phi calculation and not an Agda proof."
        ),
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
