#!/usr/bin/env python3
"""Source-bounded MATBG entropy-swing / caloric upper-bound diagnostic.

Zhang et al. Nat Commun 17, 9785 (2026), DOI 10.1038/s41467-026-76179-y
report entropy plateaus consistent with 8-fold and 4-fold combinatorial local
moment degeneracies and a strain-mediated symmetry-breaking interpretation.

This script computes only the equilibrium state-count entropy difference and
T*DeltaS per moire cell. It does NOT demonstrate an actuated strain/twist
cycle, reversibility, adiabatic temperature change, useful cooling, COP,
hysteresis closure, or same-sample QTM/caloric operation.
"""
from __future__ import annotations
import json, math

KB_MEV_PER_K = 8.617333262e-2
HIGH_COUNTS = {0: 70, 1: 56, 2: 28, 3: 8}
LOW_COUNTS = {0: 1, 1: 4, 2: 6, 3: 4}
TEMPERATURES_K = (10.0, 15.0, 20.0)


def row(nu: int):
    ratio = HIGH_COUNTS[nu] / LOW_COUNTS[nu]
    delta_s_over_kb = math.log(ratio)
    return {
        "filling": nu,
        "high_microstates": HIGH_COUNTS[nu],
        "low_microstates": LOW_COUNTS[nu],
        "delta_s_over_kB": delta_s_over_kb,
        "T_delta_S_meV_per_cell": {
            str(int(t)): KB_MEV_PER_K * t * delta_s_over_kb for t in TEMPERATURES_K
        },
    }


def main():
    receipt = {
        "source": "10.1038/s41467-026-76179-y",
        "interpretation": "equilibrium combinatorial entropy-swing scale only",
        "fillings": [row(nu) for nu in range(4)],
        "promotion_boundaries": {
            "controlled_geometry_or_strain_cycle": False,
            "reversible_cycle": False,
            "adiabatic_temperature_change": False,
            "useful_cooling": False,
            "cop": False,
            "hysteresis_and_relaxation_closure": False,
            "same_sample_qtm_entropy_cycle": False,
        },
    }
    assert receipt["fillings"][1]["high_microstates"] == 56
    assert receipt["fillings"][1]["low_microstates"] == 4
    assert abs(receipt["fillings"][1]["delta_s_over_kB"] - math.log(14.0)) < 1e-14
    assert all(r["delta_s_over_kB"] > 0 for r in receipt["fillings"])
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
