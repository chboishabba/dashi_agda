#!/usr/bin/env python3
"""Numerical replay of Zhang et al. 2026 combinatorial entropy targets.

Computes S/kB = ln C(8, nu+4) for the high-temperature plateau and
S/kB = ln C(4, nu) for the low-temperature electron-side target at
integer fillings nu=0,1,2,3. This replays the model targets only; it does
not digitize or fit the measured entropy curves.
"""

import json
import math

rows = []
for nu in range(4):
    high_count = math.comb(8, nu + 4)
    low_count = math.comb(4, nu)
    high_s = math.log(high_count)
    low_s = math.log(low_count)
    rows.append({
        "nu": nu,
        "high_temperature_microstates": high_count,
        "low_temperature_microstates": low_count,
        "high_temperature_S_over_kB": high_s,
        "low_temperature_S_over_kB": low_s,
        "delta_S_over_kB": high_s - low_s,
    })

assert [r["high_temperature_microstates"] for r in rows] == [70, 56, 28, 8]
assert [r["low_temperature_microstates"] for r in rows] == [1, 4, 6, 4]
assert all(r["delta_S_over_kB"] >= 0.0 for r in rows)

evidence = {
    "model": "Zhang-2026 combinatorial entropy target replay",
    "source_doi": "10.1038/s41467-026-76179-y",
    "fillings": rows,
    "assertions_passed": True,
    "promotion_boundaries": {
        "measured_entropy_curve_replay": False,
        "same_sample_qtm_entropy": False,
        "microscopic_mechanism_proved": False,
        "agda_kernel_receipt": False
    }
}

print(json.dumps(evidence, indent=2, sort_keys=True))
