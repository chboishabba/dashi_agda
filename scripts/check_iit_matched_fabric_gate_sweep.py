#!/usr/bin/env python3
from __future__ import annotations

import math

from iit_matched_fabric_gate_sweep import sweep_summary


def main() -> None:
    summary = sweep_summary()
    fixed = summary["fixed_recurrent_fabric_vary_gate"]
    assert fixed["binary_xor"]["iit_4_0_2023"]["distinct_phi_s"] == [2.0]
    assert fixed["binary_or"]["iit_4_0_2023"]["distinct_phi_s"] == [
        0.0,
        round(math.log2(4 / 3), 12),
        2.0,
    ]
    assert fixed["binary_and"]["iit_4_0_2023"]["zero_phi_states"] == 6
    assert fixed["ternary_trixor"]["iit_4_0_2023"]["distinct_phi_s"] == [
        round(math.log2(9), 12)
    ]
    for experiment in fixed.values():
        assert experiment["iit_4_0_2026"]["distinct_phi_s"] == [0.0]

    topology = summary["fixed_binary_xor_vary_fabric"]
    assert topology["feedforward"]["iit_4_0_2023"]["distinct_phi_s"] == [0.0]
    assert topology["recurrent_three_cell"]["iit_4_0_2023"]["distinct_phi_s"] == [2.0]
    assert topology["grid_2x2"]["iit_4_0_2023"]["distinct_phi_s"] == [0.0, 0.5]

    assert summary["boundary"]["fabric_alone_determines_phi_s"] is False
    assert summary["boundary"]["gate_alone_determines_phi_s"] is False
    print("IIT matched fabric/gate sweep: PASS")


if __name__ == "__main__":
    main()
