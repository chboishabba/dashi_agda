#!/usr/bin/env python3
"""A4 four-part proof diagnostic harness.

Checks finite numerics for the claimed A4 components:
local derivative formula, coarea strip density proxy, two-hemisphere/LRT mass
proxy, and residual positivity after the declared error rates.
"""

from __future__ import annotations

import argparse
import json
import math
import random
from pathlib import Path
from typing import Any


Vec3 = tuple[float, float, float]
EPS = 1.0e-12


def dot(a: Vec3, b: Vec3) -> float:
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]


def add(a: Vec3, b: Vec3) -> Vec3:
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2])


def scale(s: float, a: Vec3) -> Vec3:
    return (s * a[0], s * a[1], s * a[2])


def norm(a: Vec3) -> float:
    return math.sqrt(max(0.0, dot(a, a)))


def normalize(a: Vec3) -> Vec3 | None:
    n = norm(a)
    if n <= EPS:
        return None
    return scale(1.0 / n, a)


def random_unit(rng: random.Random) -> Vec3:
    z = rng.uniform(-1.0, 1.0)
    p = rng.uniform(0.0, 2.0 * math.pi)
    r = math.sqrt(max(0.0, 1.0 - z * z))
    return (r * math.cos(p), r * math.sin(p), z)


def tangent_basis(x: Vec3) -> tuple[Vec3, Vec3]:
    ref = (0.0, 0.0, 1.0) if abs(x[2]) < 0.9 else (1.0, 0.0, 0.0)
    e1 = normalize((ref[1] * x[2] - ref[2] * x[1], ref[2] * x[0] - ref[0] * x[2], ref[0] * x[1] - ref[1] * x[0]))
    assert e1 is not None
    e2 = (x[1] * e1[2] - x[2] * e1[1], x[2] * e1[0] - x[0] * e1[2], x[0] * e1[1] - x[1] * e1[0])
    return e1, e2


def cross(a: Vec3, b: Vec3) -> Vec3:
    return (
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
    )


def fval(t1: Vec3, t2: Vec3, n: Vec3) -> float | None:
    c = normalize(add(t1, t2))
    return None if c is None else dot(c, n)


def equator_pair(rng: random.Random, n: Vec3) -> tuple[Vec3, Vec3, float] | None:
    for _ in range(256):
        c = random_unit(rng)
        c = normalize((c[0] - dot(c, n) * n[0], c[1] - dot(c, n) * n[1], c[2] - dot(c, n) * n[2]))
        if c is None:
            continue
        e1 = normalize(cross(c, n))
        if e1 is None:
            continue
        gamma = rng.uniform(0.05, math.pi - 0.05)
        u = add(scale(math.cos(gamma / 2.0), c), scale(math.sin(gamma / 2.0), e1))
        v = add(scale(math.cos(gamma / 2.0), c), scale(-math.sin(gamma / 2.0), e1))
        return u, v, gamma
    return None


def numerical_gradient_norm(t1: Vec3, t2: Vec3, n: Vec3, h: float = 1.0e-6) -> float:
    grads: list[float] = []
    for base, other, first in ((t1, t2, True), (t2, t1, False)):
        e1, e2 = tangent_basis(base)
        for e in (e1, e2):
            plus = normalize(add(base, scale(h, e)))
            minus = normalize(add(base, scale(-h, e)))
            if plus is None or minus is None:
                continue
            fp = fval(plus, other, n) if first else fval(other, plus, n)
            fm = fval(minus, other, n) if first else fval(other, minus, n)
            if fp is not None and fm is not None:
                grads.append((fp - fm) / (2.0 * h))
    return math.sqrt(sum(g * g for g in grads))


def run(args: argparse.Namespace) -> dict[str, Any]:
    rng = random.Random(args.seed)
    n = normalize((0.31, -0.47, 0.83))
    assert n is not None
    gradient_errors: list[float] = []
    slab_hits = 0
    valid_pairs = 0
    hemi_pos = 0
    hemi_neg = 0
    for _ in range(args.samples):
        pair = equator_pair(rng, n)
        if pair is not None:
            t1, t2, gamma = pair
            measured = numerical_gradient_norm(t1, t2, n)
            expected = 1.0 / (math.sqrt(2.0) * math.cos(gamma / 2.0))
            gradient_errors.append(abs(measured - expected))
        a = random_unit(rng)
        b = random_unit(rng)
        fv = fval(a, b, n)
        if fv is not None:
            valid_pairs += 1
            slab_hits += int(abs(fv) <= args.eta)
        x = random_unit(rng)
        hemi_pos += int(dot(x, n) > 0.0)
        hemi_neg += int(dot(x, n) < 0.0)
    density_proxy = (slab_hits / max(valid_pairs, 1)) / max(2.0 * args.eta, EPS)
    c_lrt_proxy = min(hemi_pos, hemi_neg) / max(args.samples, 1)
    c_a4_proxy = c_lrt_proxy * c_lrt_proxy * density_proxy
    root = args.N ** -0.5
    errors = 3.0 * root + args.N ** -1
    lower = c_a4_proxy * args.eta
    return {
        "harness": "ns_a4_four_part_proof_harness",
        "scope": "finite_a4_diagnostic_not_pde_proof",
        "gradient": {
            "samples": len(gradient_errors),
            "max_abs_error": max(gradient_errors) if gradient_errors else None,
            "mean_abs_error": sum(gradient_errors) / len(gradient_errors) if gradient_errors else None,
            "formula": "1/(sqrt(2)*cos(gamma/2))",
        },
        "coarea_proxy": {
            "valid_pairs": valid_pairs,
            "eta": args.eta,
            "slab_hits": slab_hits,
            "density_proxy": density_proxy,
        },
        "lrt_proxy": {
            "positive_hemisphere_fraction": hemi_pos / args.samples,
            "negative_hemisphere_fraction": hemi_neg / args.samples,
            "c_lrt_proxy": c_lrt_proxy,
            "c_a4_proxy": c_a4_proxy,
        },
        "error_subtraction": {
            "N": args.N,
            "modeled_errors": errors,
            "lower": lower,
            "residual_margin": lower - errors,
            "residual_positive": lower > errors,
        },
        "promotion": {"a4_proved": False, "clay_ns": False, "terminal": False},
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=2000)
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--seed", type=int, default=20260609)
    parser.add_argument("--eta", type=float, default=0.05)
    parser.add_argument("--N", type=int, default=1_000_000)
    parser.add_argument("--axes", type=int, default=32)
    parser.add_argument("--json-output", type=Path)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    if args.quick:
        args.samples = min(args.samples, 6000)
        args.eta = max(args.eta, 0.1)
        args.N = max(args.N, 1_000_000_000)
    return args


def main() -> int:
    args = parse_args()
    payload = run(args)
    text = json.dumps(payload, sort_keys=True)
    if args.json_output is not None:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(text + "\n", encoding="utf-8")
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
