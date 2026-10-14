#!/usr/bin/env python3
from __future__ import annotations

import math

from iit_369_algebra_scan import algebra_summary


def main() -> None:
    summary = algebra_summary()
    z9 = summary["z9_cyclic"]
    f3sq = summary["f3_squared"]
    expected = round(math.log2(81), 12)
    assert z9["iit_4_0_2023"]["distinct_phi_s"] == [expected]
    assert f3sq["iit_4_0_2023"]["distinct_phi_s"] == [expected]
    assert z9["iit_4_0_2026"]["distinct_phi_s"] == [0.0]
    assert f3sq["iit_4_0_2026"]["distinct_phi_s"] == [0.0]
    assert summary["comparison"]["same_nine_state_cardinality"] is True
    assert summary["comparison"]["same_group_law"] is False
    assert summary["comparison"]["same_2023_system_phi_profile"] is True
    assert summary["comparison"]["system_phi_profile_identifies_group_law"] is False
    print("IIT 369 matched algebra scan: PASS")


if __name__ == "__main__":
    main()
