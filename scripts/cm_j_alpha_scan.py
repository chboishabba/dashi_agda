#!/usr/bin/env python3
"""Exploratory CM j-invariant scan for DASHI alpha diagnostics.

This is a deliberately non-promoting numerical check.  It verifies the
classical anchors j(i) ~= 1728 and j(rho) ~= 0, then asks whether simple
normalizations of small-discriminant CM j-value differences naturally return
the carrier alpha diagnostics 0.041240 and 0.085720.

No result from this script is a proof or a receipt promotion: the missing
mathematical object is still a canonical normalization map from modular
geometry to the carrier alpha lane.
"""

from __future__ import annotations

import cmath
import json
import math
from dataclasses import dataclass


ALPHA_TARGETS = {
    "alpha1": 0.041240,
    "alpha2": 0.085720,
}


def sigma_power(n: int, power: int) -> int:
    total = 0
    root = int(math.isqrt(n))
    for d in range(1, root + 1):
        if n % d == 0:
            q = n // d
            total += d**power
            if q != d:
                total += q**power
    return total


def eisenstein_e4_e6(tau: complex, terms: int = 80) -> tuple[complex, complex]:
    q = cmath.exp(2j * math.pi * tau)
    e4 = 1.0 + 0j
    e6 = 1.0 + 0j
    qn = q
    for n in range(1, terms + 1):
        e4 += 240 * sigma_power(n, 3) * qn
        e6 -= 504 * sigma_power(n, 5) * qn
        qn *= q
    return e4, e6


def j_invariant(tau: complex, terms: int = 80) -> complex:
    e4, e6 = eisenstein_e4_e6(tau, terms)
    denominator = e4**3 - e6**2
    if abs(denominator) < 1e-24:
        raise ZeroDivisionError("numerically singular modular discriminant")
    return 1728 * e4**3 / denominator


@dataclass(frozen=True)
class CMPoint:
    discriminant: int
    a: int
    b: int
    c: int
    tau: complex
    j_value: complex


def reduced_cm_points(max_abs_discriminant: int = 200) -> list[CMPoint]:
    points: list[CMPoint] = []
    for abs_d in range(3, max_abs_discriminant + 1):
        d = -abs_d
        if d % 4 not in (0, 1):
            continue
        limit = int(math.sqrt(abs_d / 3.0)) + 2
        for a in range(1, limit + 1):
            for b in range(-a, a + 1):
                if (b * b - d) % (4 * a) != 0:
                    continue
                c = (b * b - d) // (4 * a)
                if a > c:
                    continue
                if math.gcd(a, math.gcd(b, c)) != 1:
                    continue
                if abs(b) == a or a == c:
                    if b < 0:
                        continue
                tau = complex(-b / (2 * a), math.sqrt(abs_d) / (2 * a))
                try:
                    j_value = j_invariant(tau)
                except ZeroDivisionError:
                    continue
                points.append(CMPoint(d, a, b, c, tau, j_value))
    return points


def nearest(values: list[dict[str, object]], key: str, target: float) -> dict[str, object]:
    return min(values, key=lambda row: abs(float(row[key]) - target))


def main() -> None:
    i_tau = 1j
    rho_tau = complex(0.5, math.sqrt(3) / 2)
    j_i = j_invariant(i_tau)
    j_rho = j_invariant(rho_tau)

    points = reduced_cm_points()
    pair_rows: list[dict[str, object]] = []

    for left_index, left in enumerate(points):
        for right in points[left_index + 1 :]:
            lj = abs(left.j_value)
            rj = abs(right.j_value)
            diff = abs(left.j_value - right.j_value)
            scale = max(lj, rj, 1.0)
            pair_ratio = float(diff / scale)
            log_left = math.log1p(lj)
            log_right = math.log1p(rj)
            log_scale = max(log_left, log_right, 1.0)
            log_ratio = abs(log_left - log_right) / log_scale
            pair_rows.append(
                {
                    "left_D": left.discriminant,
                    "right_D": right.discriminant,
                    "pair_ratio": pair_ratio,
                    "log_ratio": log_ratio,
                }
            )

    nearest_summary = {}
    for name, target in ALPHA_TARGETS.items():
        nearest_summary[name] = {
            "target": target,
            "nearest_pair_ratio": nearest(pair_rows, "pair_ratio", target),
            "nearest_log_ratio": nearest(pair_rows, "log_ratio", target),
        }

    result = {
        "status": "exploratory_non_promoting",
        "normalization_warning": (
            "No canonical j-to-alpha normalization is defined in the repo; "
            "nearest matches under these naive normalizations do not promote "
            "alphaDerivedFromModularGeometry."
        ),
        "anchors": {
            "j_i_real": j_i.real,
            "j_i_imag": j_i.imag,
            "j_rho_abs": abs(j_rho),
        },
        "alpha_targets": ALPHA_TARGETS,
        "cm_points_scanned": len(points),
        "nearest": nearest_summary,
        "promotion": {
            "alphaDerivedFromModularGeometry": False,
            "alphaOneDerivedFromModularGeometry": False,
            "alphaTwoDerivedFromModularGeometry": False,
        },
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
