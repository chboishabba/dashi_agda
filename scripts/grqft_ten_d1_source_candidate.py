#!/usr/bin/env python3
"""Evaluate the concrete ten-slot normalized-cross-numerator candidate.

This mirrors CMP119ConcreteTenSlotCrossNumeratorCandidateExact.agda:

    N = 0
    Z = 1
    dZ = 0
    dN(h_ab) = target_ab

so dN*Z - N*dZ = target_ab exactly.

This is an executable candidate on the literal-density *type shape*.  It is not
by itself the source theorem identifying these functions with Balaban's
published CMP119 normalized expectation integrals.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path

SLOTS = ("00","01","02","03","11","12","13","22","23","33")
TARGET = {
    "00": Fraction(1),
    "01": Fraction(0),
    "02": Fraction(0),
    "03": Fraction(0),
    "11": Fraction(-1),
    "12": Fraction(0),
    "13": Fraction(0),
    "22": Fraction(-1),
    "23": Fraction(0),
    "33": Fraction(-1),
}


def encode(x: Fraction):
    return x.numerator if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    rows = {}
    for slot in SLOTS:
        n = Fraction(0)
        z = Fraction(1)
        dn = TARGET[slot]
        dz = Fraction(0)
        cross = dn * z - n * dz
        rows[slot] = {
            "N": encode(n),
            "Z": encode(z),
            "dN": encode(dn),
            "dZ": encode(dz),
            "cross_numerator": encode(cross),
            "target": encode(TARGET[slot]),
            "exact": cross == TARGET[slot],
        }

    active = TARGET["00"] + TARGET["11"] + TARGET["22"] + TARGET["33"]
    residual = {slot: encode(TARGET[slot] - Fraction(rows[slot]["cross_numerator"])) for slot in SLOTS}

    payload = {
        "contract": "grqft_ten_d1_source_candidate",
        "candidate_only": True,
        "published_cmp119_expectation_identification_claimed": False,
        "normalization": {"N": 0, "Z": 1, "dZ": 0},
        "slots": rows,
        "ten_post_sum_d1_readouts": {slot: encode(TARGET[slot]) for slot in SLOTS},
        "all_cross_numerators_exact": all(row["exact"] for row in rows.values()),
        "gr_residual_by_independent_slot": residual,
        "gr_residual_exact_zero": all(v == 0 for v in residual.values()),
        "active_stress_rho_plus_px_plus_py_plus_pz": encode(active),
        "active_stress_is_negative_two": active == Fraction(-2),
        "remaining_source_weld":
            "identify the R144/R119 post-sum finite-D1 readout with this literal-density normalized cross numerator on every symmetric slot",
    }

    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
