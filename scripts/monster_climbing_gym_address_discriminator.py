#!/usr/bin/env python3
"""Predeclared native-address Ogg/non-Ogg discriminator.

Primary statistic (one scalar per prime)
---------------------------------------
For depth-one native p-radix cells, compute Pearson occupancy deviation from
uniformity.  Standardize that observed value against a deterministic null made
by shifting all phases through one native cell period 1/p.  This controls the
strong p-dependence of cell number before any Ogg/control comparison.

Group test
----------
Contrast mean standardized score for the 15 canonical Ogg primes against the
five fixed non-Ogg controls 37,43,53,61,67.  Exhaust all C(20,5)=15504 choices
of five controls and report the two-sided |contrast| tail.

The statistic and null are intentionally single/predeclared.  The output is an
exploratory numerical receipt unless rerun on the rigorous FLINT phase-cell
bundle.  A small tail does not prove a Monster mechanism or RH.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import statistics
from pathlib import Path
from typing import Iterable, Sequence

from monster_climbing_gym_replay import load_zero_cache

OGG_PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71)
NON_OGG_CONTROLS = (37, 43, 53, 61, 67)
ALL_PRIMES = OGG_PRIMES + NON_OGG_CONTROLS


def phases(zeros: Sequence[float], prime: int) -> list[float]:
    scale = math.log(prime) / (2.0 * math.pi)
    return [(t * scale) % 1.0 for t in zeros]


def occupancy_counts(xs: Sequence[float], cells: int, shift: float = 0.0) -> list[int]:
    if cells <= 0:
        raise ValueError("cells must be positive")
    counts = [0] * cells
    for x in xs:
        y = (x + shift) % 1.0
        j = min(int(math.floor(cells * y)), cells - 1)
        counts[j] += 1
    return counts


def pearson_uniform(counts: Sequence[int]) -> float:
    if not counts:
        raise ValueError("empty occupancy vector")
    n = sum(counts)
    if n == 0:
        return 0.0
    expected = n / len(counts)
    return sum((c - expected) ** 2 / expected for c in counts)


def prime_standardized_score(
    zeros: Sequence[float],
    prime: int,
    *,
    shift_steps: int = 720,
) -> dict[str, float | int]:
    if shift_steps <= 1:
        raise ValueError("shift_steps must exceed one")
    xs = phases(zeros, prime)
    observed = pearson_uniform(occupancy_counts(xs, prime, 0.0))

    # The chi-square occupancy value is periodic under a full-cell shift up to
    # relabelling, so [0,1/p) is the complete distinct boundary-position cycle.
    shifted = []
    for i in range(shift_steps):
        delta = (i + 0.5) / (shift_steps * prime)
        shifted.append(pearson_uniform(occupancy_counts(xs, prime, delta)))

    mean = statistics.fmean(shifted)
    sd = statistics.pstdev(shifted)
    if sd == 0.0:
        z = 0.0 if observed == mean else math.copysign(math.inf, observed - mean)
    else:
        z = (observed - mean) / sd

    return {
        "prime": prime,
        "zero_count": len(zeros),
        "native_cells": prime,
        "observed_pearson": observed,
        "shift_steps": shift_steps,
        "shift_null_mean": mean,
        "shift_null_population_sd": sd,
        "standardized_z": z,
        "shift_null_min": min(shifted),
        "shift_null_max": max(shifted),
    }


def mean(values: Iterable[float]) -> float:
    xs = list(values)
    return statistics.fmean(xs)


def group_contrast(scores: dict[int, float], controls: Sequence[int]) -> float:
    control_set = set(controls)
    complement = [p for p in ALL_PRIMES if p not in control_set]
    if len(control_set) != 5 or len(complement) != 15:
        raise ValueError("balanced assignment must select five distinct controls")
    return mean(scores[p] for p in complement) - mean(scores[p] for p in controls)


def exhaustive_label_test(scores: dict[int, float]) -> dict[str, float | int]:
    actual = group_contrast(scores, NON_OGG_CONTROLS)
    all_values = [group_contrast(scores, controls) for controls in itertools.combinations(ALL_PRIMES, 5)]
    tail = sum(1 for value in all_values if abs(value) >= abs(actual))
    return {
        "actual_contrast": actual,
        "assignment_count": len(all_values),
        "two_sided_tail_count": tail,
        "two_sided_tail_fraction": tail / len(all_values),
        "minimum_contrast": min(all_values),
        "maximum_contrast": max(all_values),
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--zeros-json", type=Path, required=True)
    ap.add_argument("--shift-steps", type=int, default=720)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()

    zeros = load_zero_cache(args.zeros_json)
    rows = [prime_standardized_score(zeros, p, shift_steps=args.shift_steps) for p in ALL_PRIMES]
    score_map = {int(row["prime"]): float(row["standardized_z"]) for row in rows}
    label_test = exhaustive_label_test(score_map)

    payload = {
        "contract": "monster_climbing_gym_native_address_discriminator_v1",
        "primary_statistic": "depth-one native-cell Pearson occupancy deviation standardized by deterministic within-prime boundary-shift null",
        "ogg_primes": list(OGG_PRIMES),
        "non_ogg_controls": list(NON_OGG_CONTROLS),
        "per_prime": rows,
        "balanced_label_test": label_test,
        "predeclared_single_statistic": True,
        "input_cache_is_rigorous_zero_certificate": False,
        "confirmatory_only_after_rigorous_phase_bundle_and_locked_analysis": True,
        "promotes_monster_mechanism": False,
        "promotes_rh": False,
    }
    text = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
