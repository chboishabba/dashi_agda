#!/usr/bin/env python3
from __future__ import annotations

from iit_xor_369_stress_scan import stress_summary


def main() -> None:
    summary = stress_summary()
    assert summary["binary_recurrent_xor"]["iit_4_0_2023"]["distinct_phi_s"] == [2.0]
    assert summary["binary_xor_grid_2x2"]["iit_4_0_2023"]["distinct_phi_s"] == [0.0, 0.5]
    assert summary["ternary_recurrent_trixor"]["iit_4_0_2023"]["distinct_phi_s"] == [3.169925001442]
    assert summary["z9_recurrent_addition"]["iit_4_0_2023"]["distinct_phi_s"] == [6.339850002885]
    assert summary["f3_squared_recurrent_addition"]["iit_4_0_2023"]["distinct_phi_s"] == [6.339850002885]
    for name, experiment in summary.items():
        if name == "boundary":
            continue
        assert experiment["iit_4_0_2026"]["distinct_phi_s"] == [0.0]
    assert summary["boundary"]["system_phi_ranking_is_consciousness_ranking"] is False
    assert summary["boundary"]["historical_iit_counterexample_equals_iit4_big_phi"] is False
    print("IIT XOR/369 stress scan: PASS")


if __name__ == "__main__":
    main()
