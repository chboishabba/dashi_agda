#!/usr/bin/env python3
"""Matched 3/6/9 algebra controls for the finite IIT reference.

The same recurrent two-cell fabric ``A'=B; B'=mu(A,B)`` is used throughout.
The local operation changes while carrier size is held fixed within each
control pair:

* six states: cyclic Z/6Z-like ``hexXor`` versus noncommutative S3 composition;
* nine states: cyclic Z/9Z-like ``nonaryXor`` versus componentwise F3^2.

The algebraic non-isomorphism/separation claims are owned by Agda.  This module
only computes the corresponding finite IIT system-phi profiles.
"""
from __future__ import annotations

import json
from pathlib import Path

from iit4_finite_reference import IIT4_2023, IIT4_2026, deterministic_model, system_phi


def z6_add(a: int, b: int) -> int:
    return (a + b) % 6


# Carrier order matches HexTruthS3CarrierBridgeExact:
# id, rotate, rotate^2, swap(low,mid), swap(low,high), swap(mid,high).
S3_PERMUTATIONS = (
    (0, 1, 2),
    (1, 2, 0),
    (2, 0, 1),
    (1, 0, 2),
    (2, 1, 0),
    (0, 2, 1),
)
S3_INDEX = {permutation: index for index, permutation in enumerate(S3_PERMUTATIONS)}


def _compose_permutations(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    """Return left after right."""
    return tuple(left[right[index]] for index in range(3))


def s3_compose(a: int, b: int) -> int:
    return S3_INDEX[_compose_permutations(S3_PERMUTATIONS[a], S3_PERMUTATIONS[b])]


def z9_add(a: int, b: int) -> int:
    return (a + b) % 9


def index_to_f3_pair(index: int) -> tuple[int, int]:
    return divmod(index, 3)


def f3_pair_to_index(pair: tuple[int, int]) -> int:
    return 3 * pair[0] + pair[1]


def f3_squared_add(a: int, b: int) -> int:
    ax, ay = index_to_f3_pair(a)
    bx, by = index_to_f3_pair(b)
    return f3_pair_to_index(((ax + bx) % 3, (ay + by) % 3))


def recurrent_two_cell_step(operation):
    def step(state: tuple[int, ...]) -> tuple[int, ...]:
        a, b = state
        return b, operation(a, b)

    return step


def _scan(alphabet_size: int, operation, label: str) -> dict:
    model = deterministic_model(
        alphabet_size,
        2,
        recurrent_two_cell_step(operation),
        label=label,
    )
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


def algebra_summary() -> dict:
    z6 = _scan(6, z6_add, "Z6 cyclic addition / HexTruth hexXor chart")
    s3 = _scan(6, s3_compose, "S3 permutation composition on the six-state chart")
    z9 = _scan(9, z9_add, "Z9 cyclic addition")
    f3sq = _scan(9, f3_squared_add, "F3 squared componentwise addition")
    return {
        "contract": "iit_369_matched_algebra_scan",
        "fabric": "two-cell recurrent fabric A'=B; B'=mu(A,B)",
        "z6_cyclic": z6,
        "s3_permutation": s3,
        "z9_cyclic": z9,
        "f3_squared": f3sq,
        "six_state_comparison": {
            "same_six_state_cardinality": True,
            "same_group_law": False,
            "same_2023_system_phi_profile": (
                z6[IIT4_2023.lower()]["distinct_phi_s"]
                == s3[IIT4_2023.lower()]["distinct_phi_s"]
            ),
            "system_phi_profile_identifies_group_law": False,
            "formal_separation_owner": (
                "DASHI.Foundations.HexTruthS3CarrierBridgeExact."
                "hexCarrierChartCannotPreserveBothProducts"
            ),
        },
        "nine_state_comparison": {
            "same_nine_state_cardinality": True,
            "same_group_law": False,
            "same_2023_system_phi_profile": (
                z9[IIT4_2023.lower()]["distinct_phi_s"]
                == f3sq[IIT4_2023.lower()]["distinct_phi_s"]
            ),
            "system_phi_profile_identifies_group_law": False,
            "formal_separation_owner": (
                "DASHI.Foundations.PhaseQuotientNonaryGroupSeparationExact."
                "q9NonaryGroupIsomorphismImpossible"
            ),
        },
        "boundary": {
            "same_phi_profile_implies_same_algebra": False,
            "python_numeric_receipt_is_kernel_proof": False,
        },
    }


def main() -> None:
    summary = algebra_summary()
    output = Path(__file__).with_name("data") / "outputs" / "iit_369_algebra_scan.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
