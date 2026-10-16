#!/usr/bin/env python3
"""Numerical IIT experiment for a pure higher-order causal difference.

The two deterministic 3-bit transition laws agree whenever any one source bit
is zero; they differ only at 111 through the cubic A*B*C term.  This script is
numeric evidence only.  Agda owns the exact face-agreement/different-interior
statement in IITFaceAwareTriadicCausalPairExact.agda.

The executable regression is intentionally stronger than merely printing two
profiles: it records which current states are separated by scalar 2023
system-phi and which still collide.  That distinction is the handoff to the
full distinction/relation/big-Phi PyPhi batch.
"""
from __future__ import annotations

import argparse
import csv
import json
from itertools import product
from pathlib import Path

from iit4_finite_reference import IIT4_2023, deterministic_model, system_phi

EXPECTED_PAIRWISE = {
    (0, 0, 0): 1.5,
    (0, 0, 1): 0.0,
    (0, 1, 0): 0.0,
    (0, 1, 1): 1.5,
    (1, 0, 0): 0.0,
    (1, 0, 1): 1.5,
    (1, 1, 0): 1.5,
    (1, 1, 1): 0.0,
}

EXPECTED_TRIADIC = {
    (0, 0, 0): 3.0,
    (0, 0, 1): 0.41503749927884376,
    (0, 1, 0): 0.0,
    (0, 1, 1): 0.41503749927884376,
    (1, 0, 0): 0.0,
    (1, 0, 1): 0.41503749927884376,
    (1, 1, 0): 1.5,
    (1, 1, 1): 0.0,
}


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


def _profile(rows):
    return {tuple(row["state"]): row["phi_s"] for row in rows}


def _assert_profile(actual, expected, *, tol: float = 1.0e-12) -> None:
    assert actual.keys() == expected.keys()
    for state, target in expected.items():
        assert abs(actual[state] - target) <= tol, (state, actual[state], target)


def _write_csv(path: Path, pairwise_rows, triadic_rows) -> None:
    pairwise = _profile(pairwise_rows)
    triadic = _profile(triadic_rows)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=["state", "pairwise_phi_s_2023", "triadic_phi_s_2023", "delta"],
        )
        writer.writeheader()
        for state in sorted(pairwise):
            writer.writerow(
                {
                    "state": "".join(map(str, state)),
                    "pairwise_phi_s_2023": pairwise[state],
                    "triadic_phi_s_2023": triadic[state],
                    "delta": triadic[state] - pairwise[state],
                }
            )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json-output", type=Path)
    parser.add_argument("--csv-output", type=Path)
    args = parser.parse_args()

    face_agreement = all(
        pairwise_step(state) == triadic_step(state)
        for state in product(range(2), repeat=3)
        if 0 in state
    )
    interior_difference = pairwise_step((1, 1, 1)) != triadic_step((1, 1, 1))

    pairwise_rows = scan("pairwise-face-model", pairwise_step)
    triadic_rows = scan("triadic-face-model", triadic_step)
    pairwise = _profile(pairwise_rows)
    triadic = _profile(triadic_rows)

    _assert_profile(pairwise, EXPECTED_PAIRWISE)
    _assert_profile(triadic, EXPECTED_TRIADIC)

    separated = [list(state) for state in sorted(pairwise) if abs(pairwise[state] - triadic[state]) > 1.0e-12]
    collisions = [list(state) for state in sorted(pairwise) if abs(pairwise[state] - triadic[state]) <= 1.0e-12]

    receipt = {
        "formalism": IIT4_2023,
        "face_agreement": face_agreement,
        "interior_difference": interior_difference,
        "pairwise": pairwise_rows,
        "triadic": triadic_rows,
        "scalar_phi_separating_states": separated,
        "scalar_phi_collision_states": collisions,
        "scalar_phi_separates_some_but_not_all_states": bool(separated and collisions),
        "boundary": (
            "This is system-phi_s numerical evidence, not a full distinction/"
            "relation/big-Phi calculation and not an Agda proof."
        ),
    }
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.json_output:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(text)
    if args.csv_output:
        _write_csv(args.csv_output, pairwise_rows, triadic_rows)
    print(text, end="")


if __name__ == "__main__":
    main()
