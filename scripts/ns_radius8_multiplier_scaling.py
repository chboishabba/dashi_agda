#!/usr/bin/env python3
"""Exact scale/cutoff regression for the rational max-norm hat multiplier."""
from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from typing import Any

SCHEMA = "ns_radius8_multiplier_scaling.v1"


def q(x: Fraction) -> str:
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def digest(payload: Any) -> str:
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def hat(K: int, radius: int) -> Fraction:
    lo, mid, hi = 2 ** (K - 1), 2**K, 2 ** (K + 1)
    if radius < lo or radius > hi:
        return Fraction(0)
    if radius <= mid:
        return Fraction(radius - lo, mid - lo)
    return Fraction(hi - radius, hi - mid)


def worst_gain(K: int, R: int) -> Fraction:
    max_shift = max(1, 2 ** max(0, K - R))
    worst = Fraction(0)
    for radius in range(0, 2 ** (K + 1) + max_shift + 1):
        for shift in range(1, max_shift + 1):
            for sign in (-1, 1):
                moved = max(0, radius + sign * shift)
                worst = max(worst, abs(hat(K, moved) - hat(K, radius)))
    return worst


def build() -> dict[str, Any]:
    rows = []
    checked_pairs = 0
    for R in range(1, 9):
        shells = list(range(max(2, R), 11))
        values = [worst_gain(K, R) for K in shells]
        checked_pairs += len(shells)
        analytic = Fraction(1, 2 ** max(0, R - 1))
        rows.append(
            {
                "R": R,
                "K_min": min(shells),
                "K_max": max(shells),
                "observed_min": q(min(values)),
                "observed_max": q(max(values)),
                "analytic_gain": q(analytic),
                "scale_invariant": min(values) == max(values) == analytic,
            }
        )
    r8_symbolic = Fraction(1, 128)
    payload: dict[str, Any] = {
        "schema": SCHEMA,
        "authority": "exact_radial_reduction_for_the_max_norm_hat_only",
        "shell_radius_pairs_checked": checked_pairs,
        "rows": rows,
        "all_rows_scale_invariant": all(row["scale_invariant"] for row in rows),
        "R8_symbolic_gain": q(r8_symbolic),
        "R8_fits_one_eighth": r8_symbolic <= Fraction(1, 8),
        "promotion": {
            "radial_multiplier_equals_full_operator": False,
            "cutoff_uniform_full_far_low": False,
        },
    }
    payload["sha256"] = digest(payload)
    return payload


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--output-json", type=Path, required=True)
    ap.add_argument("--pretty", action="store_true")
    args = ap.parse_args()
    payload = build()
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(payload, sort_keys=True, indent=2 if args.pretty else None) + "\n"
    args.output_json.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
