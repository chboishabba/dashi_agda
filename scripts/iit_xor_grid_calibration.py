#!/usr/bin/env python3
from __future__ import annotations

import json
from pathlib import Path

from iit4_finite_reference import (
    IIT4_2023,
    IIT4_2026,
    deterministic_model,
    feedforward_three_cell_step,
    system_phi,
)


def xor2(a: int, b: int) -> int:
    return a ^ b


def grid2x2_step(state: tuple[int, ...]) -> tuple[int, ...]:
    north_west, north_east, south_west, south_east = state
    return (
        north_east ^ south_west,
        north_west ^ south_east,
        north_west ^ south_east,
        north_east ^ south_west,
    )


def _scan(model, formalism: str) -> dict:
    receipts = [system_phi(model, state, formalism=formalism) for state in model.states]
    values = [receipt["phi_s"] for receipt in receipts]
    mips = {
        json.dumps(receipt["mip"], sort_keys=True)
        for receipt in receipts
        if receipt["mip"] is not None
    }
    return {
        "distinct_phi_s": sorted({round(value, 12) for value in values}),
        "zero_phi_states": sum(abs(value) < 1.0e-12 for value in values),
        "mip_profiles": len(mips),
    }


def calibration_summary() -> dict:
    grid = deterministic_model(2, 4, grid2x2_step, label="repo-grid2x2-xor")
    feedforward = deterministic_model(
        2,
        3,
        feedforward_three_cell_step(xor2),
        label="feedforward-xor-control",
    )
    return {
        "recurrent_xor_grid_2x2": {
            "states_tested": len(grid.states),
            "iit_4_0_2023": _scan(grid, IIT4_2023),
            "iit_4_0_2026": _scan(grid, IIT4_2026),
        },
        "feedforward_xor_control": {
            "states_tested": len(feedforward.states),
            "iit_4_0_2023": _scan(feedforward, IIT4_2023),
            "iit_4_0_2026": _scan(feedforward, IIT4_2026),
        },
        "boundary": {
            "graph_midcut_count_is_phi_s": False,
            "historical_iit_phi_is_iit4_big_phi": False,
            "deterministic_2026_phi_s_is_zero_from_intrinsic_differentiation": True,
        },
    }


def main() -> None:
    summary = calibration_summary()
    output = Path(__file__).with_name("data") / "outputs" / "iit_xor_grid_calibration.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
