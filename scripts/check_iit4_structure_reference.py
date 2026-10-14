#!/usr/bin/env python3
from __future__ import annotations

from iit4_structure_reference import (
    big_phi,
    nonempty_relation_candidates,
    relation_phi_from_overlap,
    worked_example_calibration,
)


def main() -> None:
    assert len(nonempty_relation_candidates(("a", "B", "aB"))) == 7
    assert abs(relation_phi_from_overlap(0.07, 2, 1) - 0.035) < 1e-12
    assert abs(big_phi([0.33, 0.32, 0.07], [0.84]) - 1.56) < 1e-12

    calibration = worked_example_calibration()
    assert calibration["distinction_count"] == 3
    assert calibration["relation_count"] == 7
    assert calibration["phi_d_rounded"] == [0.33, 0.32, 0.07]
    assert calibration["big_phi_rounded"] == 1.56
    assert calibration["system_phi_s_rounded"] == 0.17
    assert calibration["big_phi_is_system_phi_s"] is False
    print("IIT4 structure reference: PASS")


if __name__ == "__main__":
    main()
