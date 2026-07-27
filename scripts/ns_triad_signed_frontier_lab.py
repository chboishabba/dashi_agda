#!/usr/bin/env python3
"""Exact finite reconnaissance for the physical-first Stage-3 triad route.

The laboratory uses Gaussian rationals and unnormalised canonical transverse
frames.  It is therefore exact for resonance, Leray projection, signed
cancellation, shell classification and raw frame coefficients.  Frame
normalisation is intentionally reported separately; this script does not
promote finite data or unnormalised coefficients to the uniform theorem.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Dict, Iterable, Iterator, List, Mapping, Sequence, Tuple

Mode = Tuple[int, int, int]
RealVec = Tuple[int, int, int]


@dataclass(frozen=True)
class Gaussian:
    re: Fraction
    im: Fraction = Fraction(0)

    def __add__(self, other: "Gaussian") -> "Gaussian":
        return Gaussian(self.re + other.re, self.im + other.im)

    def __sub__(self, other: "Gaussian") -> "Gaussian":
        return Gaussian(self.re - other.re, self.im - other.im)

    def __neg__(self) -> "Gaussian":
        return Gaussian(-self.re, -self.im)

    def __mul__(self, other: "Gaussian") -> "Gaussian":
        return Gaussian(
            self.re * other.re - self.im * other.im,
            self.re * other.im + self.im * other.re,
        )

    def conjugate(self) -> "Gaussian":
        return Gaussian(self.re, -self.im)

    def magnitude_squared(self) -> Fraction:
        return self.re * self.re + self.im * self.im

    def to_json(self) -> Mapping[str, str]:
        return {"re": str(self.re), "im": str(self.im)}


ZERO = Gaussian(Fraction(0))
ONE = Gaussian(Fraction(1))
MINUS_I = Gaussian(Fraction(0), Fraction(-1))

ComplexVec = Tuple[Gaussian, Gaussian, Gaussian]


def g(value: int | Fraction) -> Gaussian:
    return Gaussian(Fraction(value))


def vadd(a: ComplexVec, b: ComplexVec) -> ComplexVec:
    return tuple(x + y for x, y in zip(a, b))  # type: ignore[return-value]


def vsub(a: ComplexVec, b: ComplexVec) -> ComplexVec:
    return tuple(x - y for x, y in zip(a, b))  # type: ignore[return-value]


def vscale(scalar: Gaussian, vector: ComplexVec) -> ComplexVec:
    return tuple(scalar * x for x in vector)  # type: ignore[return-value]


def conjugate_vector(vector: ComplexVec) -> ComplexVec:
    return tuple(x.conjugate() for x in vector)  # type: ignore[return-value]


def bilinear_dot(a: ComplexVec, b: ComplexVec) -> Gaussian:
    total = ZERO
    for x, y in zip(a, b):
        total = total + x * y
    return total


def hermitian(a: ComplexVec, b: ComplexVec) -> Gaussian:
    return bilinear_dot(conjugate_vector(a), b)


def real_mode(mode: Mode) -> ComplexVec:
    return (g(mode[0]), g(mode[1]), g(mode[2]))


def mode_add(p: Mode, q: Mode) -> Mode:
    return (p[0] + q[0], p[1] + q[1], p[2] + q[2])


def mode_negate(k: Mode) -> Mode:
    return (-k[0], -k[1], -k[2])


def norm_squared(k: Mode) -> int:
    return k[0] * k[0] + k[1] * k[1] + k[2] * k[2]


def infinity_norm(k: Mode) -> int:
    return max(abs(k[0]), abs(k[1]), abs(k[2]))


def shell_index(k: Mode) -> int:
    """Smallest j such that |k|_infinity <= 2**j; zero maps to zero."""
    magnitude = infinity_norm(k)
    if magnitude <= 1:
        return 0
    return (magnitude - 1).bit_length()


def shell_distance(a: int, b: int) -> int:
    return abs(a - b)


def within_cutoff(k: Mode, cutoff: int) -> bool:
    return infinity_norm(k) <= cutoff


def cross(a: RealVec, b: RealVec) -> RealVec:
    return (
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
    )


def canonical_transverse_frame(k: Mode) -> Tuple[RealVec, RealVec]:
    if k == (0, 0, 0):
        raise ValueError("zero mode has no transverse frame")

    axes: Sequence[RealVec] = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
    # Select the axis least aligned with k; deterministic tie breaking is the
    # listed axis order.
    axis = min(axes, key=lambda a: abs(k[0] * a[0] + k[1] * a[1] + k[2] * a[2]))
    first = cross(k, axis)
    if first == (0, 0, 0):
        raise AssertionError(f"failed to construct frame for {k}")
    second = cross(k, first)
    if second == (0, 0, 0):
        raise AssertionError(f"degenerate second frame vector for {k}")
    return first, second


def complex_frame(k: Mode) -> Tuple[ComplexVec, ComplexVec]:
    first, second = canonical_transverse_frame(k)
    return real_mode(first), real_mode(second)


def leray_project(k: Mode, value: ComplexVec) -> ComplexVec:
    square = norm_squared(k)
    if square == 0:
        raise ValueError("Leray projection at zero mode is undefined")
    coefficient = bilinear_dot(real_mode(k), value)
    correction = vscale(
        Gaussian(coefficient.re / square, coefficient.im / square), real_mode(k)
    )
    return vsub(value, correction)


def ordered_interaction(
    k: Mode, p: Mode, q: Mode, u_p: ComplexVec, u_q: ComplexVec
) -> ComplexVec:
    scalar = bilinear_dot(u_p, real_mode(q))
    return vscale(MINUS_I, leray_project(k, vscale(scalar, u_q)))


def ordered_pair_interaction(
    k: Mode, p: Mode, q: Mode, u_p: ComplexVec, u_q: ComplexVec
) -> ComplexVec:
    return vadd(
        ordered_interaction(k, p, q, u_p, u_q),
        ordered_interaction(k, q, p, u_q, u_p),
    )


def tested_signed_coefficient(
    k: Mode,
    p: Mode,
    q: Mode,
    u_p: ComplexVec,
    u_q: ComplexVec,
    test_k: ComplexVec,
    *,
    ordered_pair: bool = True,
) -> Fraction:
    interaction = (
        ordered_pair_interaction(k, p, q, u_p, u_q)
        if ordered_pair
        else ordered_interaction(k, p, q, u_p, u_q)
    )
    return hermitian(test_k, interaction).re


def classify_scale(p: Mode, q: Mode, k: Mode, overlap: int = 3) -> str:
    jp, jq, jk = shell_index(p), shell_index(q), shell_index(k)
    if jp + overlap < jq:
        return "forced-tail-low-high"
    if jq + overlap < jp:
        return "forced-tail-high-low"
    if jk + overlap < jp and jk + overlap < jq:
        return "adversarial-high-high-low"
    return "transition-comparable"


def enumerate_modes(cutoff: int) -> List[Mode]:
    values = range(-cutoff, cutoff + 1)
    return [k for k in product(values, repeat=3) if k != (0, 0, 0)]


def enumerate_triads(cutoff: int) -> Iterator[Tuple[Mode, Mode, Mode]]:
    modes = enumerate_modes(cutoff)
    mode_set = set(modes)
    for p in modes:
        for q in modes:
            k = mode_add(p, q)
            if k in mode_set:
                yield p, q, k


def frame_norm_squared(vector: ComplexVec) -> Fraction:
    return hermitian(vector, vector).re


def triad_coefficients(p: Mode, q: Mode, k: Mode) -> Iterator[Tuple[Tuple[int, int, int], Fraction]]:
    p_frame = complex_frame(p)
    q_frame = complex_frame(q)
    k_frame = complex_frame(k)
    for pi, qi, ki in product(range(2), repeat=3):
        coefficient = tested_signed_coefficient(
            k, p, q, p_frame[pi], q_frame[qi], k_frame[ki]
        )
        yield (pi, qi, ki), coefficient


def analyse_cutoff(cutoff: int, overlap: int) -> Mapping[str, object]:
    class_sums: Dict[str, Fraction] = {}
    class_signed_sums: Dict[str, Fraction] = {}
    class_max: Dict[str, Tuple[Fraction, Tuple[Mode, Mode, Mode], Tuple[int, int, int]]] = {}
    triad_count = 0
    coefficient_count = 0

    for p, q, k in enumerate_triads(cutoff):
        triad_count += 1
        class_name = classify_scale(p, q, k, overlap)
        for frame_tag, coefficient in triad_coefficients(p, q, k):
            coefficient_count += 1
            magnitude = abs(coefficient)
            class_sums[class_name] = class_sums.get(class_name, Fraction(0)) + magnitude
            class_signed_sums[class_name] = (
                class_signed_sums.get(class_name, Fraction(0)) + coefficient
            )
            previous = class_max.get(class_name)
            if previous is None or magnitude > previous[0]:
                class_max[class_name] = (magnitude, (p, q, k), frame_tag)

    maxima = {
        name: {
            "magnitude": str(value[0]),
            "p": value[1][0],
            "q": value[1][1],
            "k": value[1][2],
            "frame": value[2],
            "shells": (
                shell_index(value[1][0]),
                shell_index(value[1][1]),
                shell_index(value[1][2]),
            ),
        }
        for name, value in class_max.items()
    }

    return {
        "cutoff": cutoff,
        "overlap": overlap,
        "mode_count": len(enumerate_modes(cutoff)),
        "triad_count": triad_count,
        "coefficient_count": coefficient_count,
        "absolute_class_sums": {k: str(v) for k, v in class_sums.items()},
        "signed_class_sums": {k: str(v) for k, v in class_signed_sums.items()},
        "scaled_absolute_class_sums": {
            k: str(cutoff * cutoff * v) for k, v in class_sums.items()
        },
        "extremisers": maxima,
        "warning": (
            "Coefficients use exact unnormalised canonical transverse frames. "
            "Use them to test cancellation/null geometry, not as final normalised constants."
        ),
    }


def verify_geometry(cutoff: int, overlap: int) -> None:
    for p, q, k in enumerate_triads(cutoff):
        assert mode_add(p, q) == k
        assert infinity_norm(k) <= infinity_norm(p) + infinity_norm(q)
        assert infinity_norm(p) <= infinity_norm(k) + infinity_norm(q)
        assert infinity_norm(q) <= infinity_norm(k) + infinity_norm(p)
        class_name = classify_scale(p, q, k, overlap)
        jp, jq, jk = shell_index(p), shell_index(q), shell_index(k)
        if class_name == "forced-tail-low-high":
            assert jp + overlap < jq
        elif class_name == "forced-tail-high-low":
            assert jq + overlap < jp
        elif class_name == "adversarial-high-high-low":
            assert jk + overlap < jp and jk + overlap < jq


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cutoff", type=int, default=2)
    parser.add_argument("--overlap", type=int, default=3)
    parser.add_argument("--verify", action="store_true")
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.cutoff < 1:
        raise SystemExit("--cutoff must be positive")
    if args.overlap < 0:
        raise SystemExit("--overlap must be nonnegative")
    if args.verify:
        verify_geometry(args.cutoff, args.overlap)
    result = analyse_cutoff(args.cutoff, args.overlap)
    print(json.dumps(result, indent=2 if args.pretty else None, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
