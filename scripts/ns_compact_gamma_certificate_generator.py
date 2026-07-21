#!/usr/bin/env python3
"""Generate exact finite-core certificates and explicit analytic-tail obligations.

This is a certificate-generation lane, not a theorem prover.  Every numerical
quantity is serialized as an exact rational.  Finite cores are exhaustively
checked over deterministic integer grids.  Infinite-range claims remain
explicit obligations and all promotion flags stay false until an Agda theorem
supplies those obligations.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable

SCHEMA = "ns_compact_gamma_certificate_bundle.v1"


def q(x: Fraction | int) -> str:
    x = Fraction(x)
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def digest(payload: Any) -> str:
    raw = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(raw).hexdigest()


def vectors(radius: int) -> Iterable[tuple[int, int, int]]:
    for v in itertools.product(range(-radius, radius + 1), repeat=3):
        if v != (0, 0, 0):
            yield v


def norm_sq(v: tuple[int, int, int]) -> int:
    return sum(x * x for x in v)


def dot(a: tuple[int, int, int], b: tuple[int, int, int]) -> int:
    return sum(x * y for x, y in zip(a, b))


def adjacent_core(radius: int) -> dict[str, Any]:
    # Exhaustively refute unconditional adjacent contraction on a finite exact
    # amplitude grid.  The theorem route must therefore include admissibility or
    # a remainder term rather than assert A_{j+1} <= rho A_j universally.
    amplitudes = [Fraction(1, 8), Fraction(1, 4), Fraction(1, 2), Fraction(1), Fraction(2), Fraction(4), Fraction(8)]
    ratios = [b / a for a in amplitudes for b in amplitudes]
    worst = max(ratios)
    return {
        "domain": {"amplitude_grid": [q(x) for x in amplitudes], "radius": radius},
        "checked_pairs": len(ratios),
        "max_ratio": q(worst),
        "unconditional_contraction_refuted": worst > 1,
        "required_tail_obligation": {
            "name": "adjacent_recurrence_with_geometric_remainder",
            "quantifiers": ["every shell K", "every distance n", "every admissible periodic Fourier state u"],
            "statement": "A(K,n+1) <= rho*A(K,n) + r(K,n), rho < 1, r(K,n) <= Cr*theta^n*Envelope(K,u), theta < 1",
        },
    }


def near_triad_core(radius: int, delta: Fraction) -> dict[str, Any]:
    # Exact scalar surrogate for the trilinear oddness and Young bookkeeping.
    # Enumerate integer amplitudes/signs; Q=abc, D=a^2+b^2+c^2, E=1+a^2+b^2+c^2.
    vals = range(-radius, radius + 1)
    checked = 0
    positive = negative = 0
    max_required = Fraction(0)
    oddness_ok = True
    for a, b, c in itertools.product(vals, repeat=3):
        if a == b == c == 0:
            continue
        checked += 1
        Q = Fraction(a * b * c)
        Qr = Fraction((-a) * (-b) * (-c))
        oddness_ok = oddness_ok and (Qr == -Q)
        positive += Q > 0
        negative += Q < 0
        D = Fraction(a * a + b * b + c * c)
        E = Fraction(1 + a * a + b * b + c * c)
        required = max(Fraction(0), (abs(Q) - delta * D) / E)
        max_required = max(max_required, required)
    return {
        "domain": {"integer_amplitude_radius": radius},
        "checked_configurations": checked,
        "delta": q(delta),
        "candidate_C_delta": q(max_required),
        "oddness_exact": oddness_ok,
        "positive_count": positive,
        "negative_count": negative,
        "signed_coercivity_refuted_on_core": positive > 0 and negative > 0,
        "finite_core_absorption_verified": True,
        "required_tail_obligation": {
            "name": "near_triad_uniform_tail_majorant",
            "quantifiers": ["every shell K", "every Galerkin cutoff N", "every admissible u and tangent h"],
            "statement": "abs(Qnear(K,N,u,h)) <= delta*D(K,h) + Cdelta*E(K,u,h)",
            "candidate_constants": {"delta": q(delta), "C_delta": q(max_required)},
        },
    }


def far_low_core(radius: int, R: int) -> dict[str, Any]:
    # Exact polynomial multiplier surrogate m(x)=x^2 on normalized rational
    # coordinates.  Verify |m(q+p)-m(q)| <= C|p| for |q|<=1, |p|<=2^-R.
    step = Fraction(1, 2**R)
    qs = [Fraction(i, radius) for i in range(-radius, radius + 1)]
    ps = [i * step for i in range(-radius, radius + 1)]
    C = Fraction(0)
    checked = 0
    for x in qs:
        for p in ps:
            if p == 0:
                continue
            checked += 1
            ratio = abs((x + p) ** 2 - x**2) / abs(p)
            C = max(C, ratio)
    normalized = C * step
    return {
        "domain": {"q_grid_radius": radius, "R": R},
        "checked_configurations": checked,
        "mean_value_constant": q(C),
        "normalized_radius_gain": q(normalized),
        "fits_one_eighth_budget": normalized <= Fraction(1, 8),
        "required_tail_obligation": {
            "name": "periodic_far_low_commutator_tail",
            "quantifiers": ["every shell K", "every cutoff N", "every low mode p with |p|<=2^(K-R)"],
            "statement": "|m_K(k)-m_K(q)| <= Cm*2^-K*|p| and the induced commutator constant at R=8 is <=1/8",
        },
    }


def geometric_sum(first: Fraction, ratio: Fraction) -> Fraction:
    if not (0 <= ratio < 1):
        raise ValueError("geometric ratio must lie in [0,1)")
    return first / (1 - ratio)


def far_high_core(R: int, alpha: Fraction) -> dict[str, Any]:
    ratio = Fraction(1, 2) ** alpha.numerator if alpha.denominator == 1 else None
    # Use the exact selected alpha=3/2 via a safe rational majorant 2^{-n}.
    # This is deliberately weaker but exact and sufficient for the finite budget.
    majorant_ratio = Fraction(1, 2)
    first = majorant_ratio**R
    bound = geometric_sum(first, majorant_ratio)
    return {
        "R": R,
        "alpha": q(alpha),
        "exact_rational_majorant_ratio": q(majorant_ratio),
        "geometric_tail_majorant": q(bound),
        "fits_one_eighth_budget": bound <= Fraction(1, 8),
        "required_tail_obligation": {
            "name": "periodic_far_high_sobolev_paraproduct_tail",
            "quantifiers": ["every shell K", "every cutoff N", "every u in H^s with s>5/2"],
            "statement": "sum_{j>=K+R} 2^(5j/2)||P_j u||_2 <= Cs*2^{-(s-5/2)R}||u||_{H^s}, with the full paraproduct constant <=1/8 at R=8",
        },
    }


def coverage_contract() -> dict[str, Any]:
    return {
        "fixed_absolute_floor_route_rejected": True,
        "allowed_routes": ["normalized_packet_energy", "adaptive_packet_floor", "direct_small_or_diffuse_BKM_branch"],
        "required_tail_obligation": {
            "name": "official_data_coverage",
            "quantifiers": ["every smooth divergence-free finite-energy initial datum"],
            "statement": "zero data are globally smooth; every nonzero trajectory either enters a normalized/adaptive compact-Gamma chart with controlled switching or satisfies a direct BKM continuation criterion",
        },
    }


def build(radius: int, R: int) -> dict[str, Any]:
    leaves = {
        "adjacent_shell": adjacent_core(radius),
        "near_triad": near_triad_core(radius, Fraction(1, 4)),
        "far_low": far_low_core(radius, R),
        "far_high": far_high_core(R, Fraction(3, 2)),
        "official_coverage": coverage_contract(),
    }
    core = {
        "schema": SCHEMA,
        "authority": "exact_finite_core_plus_unproved_analytic_tail_obligations",
        "finite_arithmetic": "fractions.Fraction",
        "finite_core_exhaustive": True,
        "leaves": leaves,
        "promotion": {"agda_inhabitant": False, "full_ns": False, "clay": False},
    }
    core["certificate_sha256"] = digest(core)
    return core


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--output-json", type=Path, required=True)
    ap.add_argument("--radius", type=int, default=4)
    ap.add_argument("--R", type=int, default=8)
    ap.add_argument("--pretty", action="store_true")
    args = ap.parse_args()
    payload = build(args.radius, args.R)
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(payload, sort_keys=True, indent=2 if args.pretty else None) + "\n"
    args.output_json.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
