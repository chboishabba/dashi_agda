#!/usr/bin/env python3
from __future__ import annotations

import math

from iit4_finite_reference import (
    IIT4_2023,
    IIT4_2026,
    deterministic_model,
    directional_partitions,
    recurrent_three_cell_step,
    feedforward_three_cell_step,
    system_phi,
)


def xor2(a: int, b: int) -> int:
    return a ^ b


def or2(a: int, b: int) -> int:
    return int(bool(a) or bool(b))


def tri_xor(a: int, b: int) -> int:
    return (a + b) % 3


def values(model, version: str) -> set[float]:
    return {
        round(system_phi(model, state, formalism=version)["phi_s"], 12)
        for state in model.states
    }


def main() -> None:
    assert len(directional_partitions(3)) == 54

    xor_model = deterministic_model(2, 3, recurrent_three_cell_step(xor2))
    assert values(xor_model, IIT4_2023) == {2.0}
    assert values(xor_model, IIT4_2026) == {0.0}

    or_model = deterministic_model(2, 3, recurrent_three_cell_step(or2))
    assert values(or_model, IIT4_2023) == {
        0.0,
        round(math.log2(4 / 3), 12),
        2.0,
    }
    assert values(or_model, IIT4_2026) == {0.0}

    tri_model = deterministic_model(3, 3, recurrent_three_cell_step(tri_xor))
    assert values(tri_model, IIT4_2023) == {round(math.log2(9), 12)}
    assert values(tri_model, IIT4_2026) == {0.0}

    ff_model = deterministic_model(2, 3, feedforward_three_cell_step(xor2))
    assert values(ff_model, IIT4_2023) == {0.0}

    receipt = system_phi(xor_model, (0, 0, 0), formalism=IIT4_2023)
    assert receipt["formalism"] == IIT4_2023
    assert receipt["phi_s"] == 2.0
    assert receipt["mip"]["affected_connection_count"] > 0
    assert receipt["intrinsic_information"] == 0.0

    print("IIT4 finite reference: PASS")


if __name__ == "__main__":
    main()
