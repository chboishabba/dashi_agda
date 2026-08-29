#!/usr/bin/env python3
"""Round232 exploratory audit of the exact opposite-helicity cross symbol.

This script is deliberately diagnostic, not proof authority.  It constructs a
normalized helical basis h_s(k) satisfying i k-hat x h_s = s h_s, evaluates
|h_+(p) x h_-(q)|^2, and checks the gauge-invariant angular formula

    |h_+(p) x h_-(q)|^2 = ((3-c)(1+c))/4,
    c = p-hat . q-hat.

It then probes the three Bony regimes used by the Package-A search:
  * FL: no generic scale-ratio gain;
  * HH->L: exact anti-parallel null gain ~ |k|/sqrt(|p||q|);
  * CC: no generic half-derivative gain.

A successful run is evidence for theorem design only.  It is not an Agda or
analytic proof receipt.
"""

from __future__ import annotations

import cmath
import math
import random
from typing import Iterable, Sequence

Vec3 = tuple[complex, complex, complex]
RealVec3 = tuple[float, float, float]


def dot_real(a: Sequence[float], b: Sequence[float]) -> float:
    return sum(x * y for x, y in zip(a, b))


def norm_real(a: Sequence[float]) -> float:
    return math.sqrt(dot_real(a, a))


def cross(a: Sequence[complex], b: Sequence[complex]) -> Vec3:
    return (
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
    )


def norm_sq_complex(a: Sequence[complex]) -> float:
    return sum((z.conjugate() * z).real for z in a)


def normalize_real(a: Sequence[float]) -> RealVec3:
    r = norm_real(a)
    if r == 0.0:
        raise ValueError("zero mode")
    return tuple(x / r for x in a)  # type: ignore[return-value]


def helical_vector(k: Sequence[float], sign: int) -> Vec3:
    """Return one normalized helicity eigenvector, with arbitrary smooth gauge."""
    if sign not in (-1, 1):
        raise ValueError("sign must be +/-1")
    kh = normalize_real(k)
    ref: RealVec3 = (0.0, 0.0, 1.0)
    if abs(dot_real(kh, ref)) > 0.9:
        ref = (0.0, 1.0, 0.0)
    e1_raw = cross(ref, kh)
    e1 = normalize_real(tuple(float(z.real) for z in e1_raw))
    e2_raw = cross(kh, e1)
    e2 = tuple(float(z.real) for z in e2_raw)
    inv_sqrt2 = 1.0 / math.sqrt(2.0)
    return tuple(
        inv_sqrt2 * (e1[j] + 1j * sign * e2[j]) for j in range(3)
    )  # type: ignore[return-value]


def opposite_symbol_sq(p: Sequence[float], q: Sequence[float]) -> float:
    hp = helical_vector(p, +1)
    hm = helical_vector(q, -1)
    return norm_sq_complex(cross(hp, hm))


def angular_formula_sq(p: Sequence[float], q: Sequence[float]) -> float:
    c = dot_real(p, q) / (norm_real(p) * norm_real(q))
    return ((3.0 - c) * (1.0 + c)) / 4.0


def hh_upper_sq(p: Sequence[float], q: Sequence[float]) -> float:
    k = tuple(p[j] + q[j] for j in range(3))
    return norm_real(k) ** 2 / (2.0 * norm_real(p) * norm_real(q))


def close(a: float, b: float, tol: float = 5e-12) -> bool:
    return abs(a - b) <= tol * max(1.0, abs(a), abs(b))


def random_nonzero_mode(radius: int = 20) -> tuple[int, int, int]:
    while True:
        v = tuple(random.randint(-radius, radius) for _ in range(3))
        if v != (0, 0, 0):
            return v  # type: ignore[return-value]


def verify_formula(samples: int = 5000) -> float:
    worst = 0.0
    for _ in range(samples):
        p = random_nonzero_mode()
        q = random_nonzero_mode()
        lhs = opposite_symbol_sq(p, q)
        rhs = angular_formula_sq(p, q)
        worst = max(worst, abs(lhs - rhs))
        if not close(lhs, rhs):
            raise AssertionError((p, q, lhs, rhs))
    return worst


def verify_hh_bound(samples: int = 5000) -> float:
    worst_ratio = 0.0
    for _ in range(samples):
        p = random_nonzero_mode()
        q = random_nonzero_mode()
        lhs = opposite_symbol_sq(p, q)
        rhs = hh_upper_sq(p, q)
        # The estimate follows from 3-c <= 4 and resonance.
        if lhs > rhs + 1e-11 * max(1.0, rhs):
            raise AssertionError((p, q, lhs, rhs))
        if rhs > 0:
            worst_ratio = max(worst_ratio, lhs / rhs)
    return worst_ratio


def regime_table() -> list[tuple[str, int, float, float]]:
    rows: list[tuple[str, int, float, float]] = []
    for R in (4, 8, 16, 32, 64, 128):
        # FL: q remains low and orthogonal to p. Symbol stays sqrt(3)/2.
        p_fl = (R, 0, 0)
        q_fl = (0, 1, 0)
        fl = math.sqrt(opposite_symbol_sq(p_fl, q_fl))
        rows.append(("FL", R, fl, 1.0 / R))

        # HH->L: p and q are nearly anti-parallel, output k=(0,1,0).
        p_hh = (R, 0, 0)
        q_hh = (-R, 1, 0)
        hh = math.sqrt(opposite_symbol_sq(p_hh, q_hh))
        hh_scale = norm_real((0, 1, 0)) / math.sqrt(norm_real(p_hh) * norm_real(q_hh))
        rows.append(("HH", R, hh, hh_scale))

        # CC: p,q are orthogonal and comparable. Symbol stays sqrt(3)/2.
        p_cc = (R, 0, 0)
        q_cc = (0, R, 0)
        cc = math.sqrt(opposite_symbol_sq(p_cc, q_cc))
        rows.append(("CC", R, cc, R ** -0.5))
    return rows


def main() -> None:
    random.seed(232)
    worst_formula = verify_formula()
    worst_hh_ratio = verify_hh_bound()

    print("Round232 opposite-helicity symbol audit")
    print(f"max angular-formula error: {worst_formula:.3e}")
    print(f"max HH bound ratio:       {worst_hh_ratio:.12f}")
    print()
    print("region   R        |B_+-|          comparison-scale")
    for region, radius, symbol, scale in regime_table():
        print(f"{region:>4}  {radius:4d}   {symbol:14.10f}   {scale:14.10f}")

    expected_cc = math.sqrt(3.0) / 2.0
    if not close(math.sqrt(opposite_symbol_sq((1, 0, 0), (0, 1, 0))), expected_cc):
        raise AssertionError("CC witness changed")

    print()
    print("DECISION:")
    print("  HH->L has the exact anti-parallel null gain |k|/sqrt(2|p||q|).")
    print("  FL has no generic pointwise |q|/|p| gain in the bare mixed symbol.")
    print("  CC has no pointwise half-derivative gain; the orthogonal family stays sqrt(3)/2.")
    print("  Therefore pointwise-symbol estimates alone cannot close the Leray endpoint.")


if __name__ == "__main__":
    main()
