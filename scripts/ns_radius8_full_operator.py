#!/usr/bin/env python3
"""Exact finite weighted-kernel diagnostic for the full far-low Fourier operator.

The finite model includes two rational divergence-free polarizations, Biot--Savart,
the linearized vorticity triad, output Leray projection, the exact dyadic
commutator multiplier, convolution multiplicity, and Schur row/column sums.
It is a finite falsifier/certificate candidate, not a universal theorem.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable

from ns_periodic_concrete_proof_program import hat_multiplier, modes, q, vadd, vmax

SCHEMA = "ns_radius8_full_operator.v1"
Vec = tuple[Fraction, Fraction, Fraction]
Mode = tuple[int, int, int]


def digest(payload: Any) -> str:
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def as_vec(k: Mode) -> Vec:
    return tuple(Fraction(x) for x in k)  # type: ignore[return-value]


def add(a: Vec, b: Vec) -> Vec:
    return tuple(x + y for x, y in zip(a, b))  # type: ignore[return-value]


def sub(a: Vec, b: Vec) -> Vec:
    return tuple(x - y for x, y in zip(a, b))  # type: ignore[return-value]


def scale(c: Fraction, a: Vec) -> Vec:
    return tuple(c * x for x in a)  # type: ignore[return-value]


def dot(a: Vec, b: Vec) -> Fraction:
    return sum((x * y for x, y in zip(a, b)), Fraction(0))


def cross(a: Vec, b: Vec) -> Vec:
    return (
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
    )


def l1(a: Vec) -> Fraction:
    return sum((abs(x) for x in a), Fraction(0))


def normalize_l1(a: Vec) -> Vec:
    n = l1(a)
    if n == 0:
        raise ValueError("zero polarization")
    return scale(Fraction(1, 1) / n, a)


def polarizations(k: Mode) -> tuple[Vec, Vec]:
    kv = as_vec(k)
    axes: tuple[Vec, ...] = ((Fraction(1), Fraction(0), Fraction(0)), (Fraction(0), Fraction(1), Fraction(0)), (Fraction(0), Fraction(0), Fraction(1)))
    axis = min(axes, key=lambda e: abs(dot(kv, e)))
    first = normalize_l1(cross(kv, axis))
    second = normalize_l1(cross(kv, first))
    assert dot(kv, first) == 0 and dot(kv, second) == 0
    return first, second


def norm_sq(k: Mode) -> int:
    return sum(x * x for x in k)


def biot_savart(k: Mode, omega: Vec) -> Vec:
    return scale(Fraction(1, norm_sq(k)), cross(as_vec(k), omega))


def triad(p: Mode, qq: Mode, omega_p: Vec, omega_q: Vec) -> Vec:
    qv = as_vec(qq)
    return sub(
        scale(dot(omega_p, qv), biot_savart(qq, omega_q)),
        scale(dot(biot_savart(p, omega_p), qv), omega_q),
    )


def linearized(p: Mode, qq: Mode, omega_p: Vec, eta_q: Vec) -> Vec:
    return add(triad(p, qq, omega_p, eta_q), triad(qq, p, eta_q, omega_p))


def leray(k: Mode, v: Vec) -> Vec:
    kv = as_vec(k)
    return sub(v, scale(dot(kv, v) / Fraction(norm_sq(k)), kv))


def support_modes(K: int) -> list[Mode]:
    cutoff = 2 ** (K + 1)
    return [k for k in modes(cutoff) if hat_multiplier(K, k) != 0]


def build(K: int, R: int) -> dict[str, Any]:
    if K <= R:
        low_radius = 1
    else:
        low_radius = 2 ** (K - R)
    low_modes = list(modes(low_radius))
    source_modes = support_modes(K)
    pol_cache = {k: polarizations(k) for k in set(low_modes + source_modes)}

    entries: dict[tuple[Mode, Mode, int], Fraction] = defaultdict(Fraction)
    max_single = Fraction(0)
    witness: dict[str, Any] | None = None
    checked = 0

    for p in low_modes:
        for qq in source_modes:
            k = vadd(p, qq)
            if k == (0, 0, 0):
                continue
            multiplier = abs(hat_multiplier(K, k) - hat_multiplier(K, qq))
            if multiplier == 0:
                continue
            for lp, omega_p in enumerate(pol_cache[p]):
                for lq, eta_q in enumerate(pol_cache[qq]):
                    checked += 1
                    projected = leray(k, linearized(p, qq, omega_p, eta_q))
                    value = multiplier * l1(projected)
                    entries[(k, qq, lq)] += value
                    if value > max_single:
                        max_single = value
                        witness = {"p": p, "q": qq, "k": k, "background_polarization": lp, "source_polarization": lq, "value": q(value)}

    row_sums: dict[Mode, Fraction] = defaultdict(Fraction)
    col_sums: dict[tuple[Mode, int], Fraction] = defaultdict(Fraction)
    for (k, qq, lq), value in entries.items():
        row_sums[k] += value
        col_sums[(qq, lq)] += value
    row_bound = max(row_sums.values(), default=Fraction(0))
    column_bound = max(col_sums.values(), default=Fraction(0))
    schur_product = row_bound * column_bound

    payload: dict[str, Any] = {
        "schema": SCHEMA,
        "authority": "exact_finite_full_operator_weighted_l1_schur_diagnostic",
        "K": K,
        "R": R,
        "low_radius": low_radius,
        "low_mode_count": len(low_modes),
        "source_mode_count": len(source_modes),
        "checked_polarized_interactions": checked,
        "nonzero_matrix_entries": len(entries),
        "max_single_contribution": q(max_single),
        "row_bound": q(row_bound),
        "column_bound": q(column_bound),
        "schur_product": q(schur_product),
        "witness": witness,
        "components": {
            "divergence_free_polarizations": 2,
            "polarization_normalization": "exact rational l1",
            "biot_savart": "|p|^-2 p cross omega",
            "linearized_triad": "T(p,q;bar_omega,eta)+T(q,p;eta,bar_omega)",
            "output_leray": true,
            "dyadic_commutator": true,
            "fourier_normalization": "coefficient/unitary",
            "convolution_multiplicity": "summed exactly in matrix entries",
        },
        "promotion": {
            "finite_l1_model_equals_official_norm": False,
            "cutoff_uniform_schur_bound": False,
            "universal_far_low": False,
        },
    }
    payload["sha256"] = digest(payload)
    return payload


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--output-json", type=Path, required=True)
    ap.add_argument("--K", type=int, default=2)
    ap.add_argument("--R", type=int, default=2)
    ap.add_argument("--pretty", action="store_true")
    args = ap.parse_args()
    payload = build(args.K, args.R)
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(payload, sort_keys=True, indent=2 if args.pretty else None) + "\n"
    args.output_json.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
