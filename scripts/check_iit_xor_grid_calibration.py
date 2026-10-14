#!/usr/bin/env python3
from __future__ import annotations

from iit_xor_grid_calibration import calibration_summary


def main() -> None:
    summary = calibration_summary()
    grid = summary["recurrent_xor_grid_2x2"]
    assert grid["states_tested"] == 16
    assert grid["iit_4_0_2023"]["distinct_phi_s"] == [0.0, 0.5]
    assert grid["iit_4_0_2023"]["zero_phi_states"] == 12
    assert grid["iit_4_0_2026"]["distinct_phi_s"] == [0.0]
    assert grid["iit_4_0_2026"]["zero_phi_states"] == 16

    control = summary["feedforward_xor_control"]
    assert control["iit_4_0_2023"]["distinct_phi_s"] == [0.0]
    assert control["iit_4_0_2026"]["distinct_phi_s"] == [0.0]

    assert summary["boundary"]["graph_midcut_count_is_phi_s"] is False
    assert summary["boundary"]["historical_iit_phi_is_iit4_big_phi"] is False
    print("IIT XOR-grid calibration: PASS")


if __name__ == "__main__":
    main()
