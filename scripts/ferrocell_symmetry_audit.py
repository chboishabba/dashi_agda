#!/usr/bin/env python3
"""A reproducible, standard-library-only FERROCELL POLARISER NULL MODEL.

Not a reconstruction of a particular image and not an entanglement test.
Forward model: I(theta) = sin²[2(theta-alpha-beta)] sin²(delta/2).
Here alpha is a hypothetical director offset, beta a polariser offset, and
retardance delta is constant on the analyzed circle. Intensity is normalised
before camera response. Any measured ring can have nuisance illumination.
"""
from __future__ import annotations

import argparse
import cmath
import json
import math
from typing import Sequence

TAU = 2 * math.pi


def model(n: int = 72, *, director: float = 0., polariser: float = 0.,
          retardance: float = math.pi, illumination_six: float = 0.,
          illumination_three: float = 0.) -> list[float]:
    if n < 32:
        raise ValueError("Use at least 32 angular samples to resolve m=9")
    if abs(illumination_six) + abs(illumination_three) > 1:
        raise ValueError("Keep illumination nonnegative")
    scale = math.sin(retardance / 2) ** 2
    return [scale * math.sin(2 * (TAU * j / n - director - polariser)) ** 2
            * (1 + illumination_six * math.cos(6 * TAU * j / n)
               + illumination_three * math.cos(3 * TAU * j / n))
            for j in range(n)]


def dft_magnitude(samples: Sequence[float], harmonic: int) -> float:
    n = len(samples)
    return abs(sum(v * cmath.exp(-1j * TAU * harmonic * j / n)
                   for j, v in enumerate(samples)) / n)


def signature(samples: Sequence[float], harmonics=range(13)) -> dict[str, float]:
    return {str(k): round(dft_magnitude(samples, k), 12) for k in harmonics}


def audit(n: int = 72) -> dict:
    if n % 8:
        raise ValueError("audit samples must be a multiple of eight for exact sector rotations")
    baseline = model(n)
    quarter = [baseline[(j + n // 4) % n] for j in range(n)]
    polarised = model(n, polariser=math.pi / 4)
    reversed_director = model(n, director=math.pi)
    six_nuisance = model(n, illumination_six=0.25)
    three_nuisance = model(n, illumination_three=0.25)
    return {
        "model_status": "idealised_classical_null_not_video_reconstruction",
        "samples": n,
        "baseline_fourier_amplitudes": signature(baseline),
        "sixfold_illumination_fourier_amplitudes": signature(six_nuisance),
        "threefold_illumination_fourier_amplitudes": signature(three_nuisance),
        "max_quarter_rotation_error": max(abs(x-y) for x,y in zip(baseline, quarter)),
        "max_field_director_reversal_error": max(abs(x-y) for x,y in zip(baseline, reversed_director)),
        "max_polariser_shift_complement_error": max(abs(x+y-1) for x,y in zip(baseline, polarised)),
        "quantum_or_torus_established": False,
    }


def self_test() -> None:
    for n in (72, 96, 144):
        a = audit(n)
        assert a["max_quarter_rotation_error"] < 1e-12, a
        assert a["max_field_director_reversal_error"] < 1e-12, a
        assert a["max_polariser_shift_complement_error"] < 1e-12, a
        h = a["baseline_fourier_amplitudes"]
        assert abs(h["0"] - 0.5) < 1e-12, h
        assert abs(h["4"] - 0.25) < 1e-12, h
        for k in (1,2,3,5,6,7,8,9,10,11,12):
            assert abs(h[str(k)]) < 1e-12, (k, h)
        assert a["sixfold_illumination_fourier_amplitudes"]["6"] > 0.01
        assert a["threefold_illumination_fourier_amplitudes"]["3"] > 0.01


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--samples", type=int, default=72)
    p.add_argument("--self-test", action="store_true")
    p.add_argument("--json", type=str, default="")
    args = p.parse_args()
    if args.self_test:
        self_test()
    result = audit(args.samples)
    output = json.dumps(result, indent=2, sort_keys=True)
    if args.json:
        with open(args.json, "w", encoding="utf-8") as f:
            f.write(output + "\n")
    else:
        print(output)


if __name__ == "__main__":
    main()
