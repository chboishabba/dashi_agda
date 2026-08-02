#!/usr/bin/env python3
"""Exact reconnaissance for projected-axis off-diagonal matrix coherence."""
from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction as F
from itertools import permutations, product
from pathlib import Path

import ns_quartic_localized_helicity_reconnaissance as base

Axis = tuple[int, int, int]
Matrix = list[list[F]]


def matrix_vector(matrix: Matrix, value: base.V) -> base.V:
    out: base.V = []
    for row in matrix:
        total = base.c()
        for coefficient, entry in zip(row, value, strict=True):
            total = base.ca(total, base.cs(coefficient, entry))
        out.append(total)
    return out


def matrix_multiply(left: Matrix, right: Matrix) -> Matrix:
    return [[sum(left[i][h] * right[h][j] for h in range(3)) for j in range(3)] for i in range(3)]


def projection_matrix(mode: base.M) -> Matrix:
    norm = F(base.n2(mode))
    return [[(F(1) if i == j else F(0)) - F(mode[i] * mode[j], norm) for j in range(3)] for i in range(3)]


def reflection_symbol(mode: base.M, axis: Axis) -> Matrix | None:
    projection = projection_matrix(mode)
    projected_axis = [sum(projection[i][j] * F(axis[j]) for j in range(3)) for i in range(3)]
    projected_norm = sum(entry * entry for entry in projected_axis)
    if projected_norm == 0:
        return None
    return [[F(2) * projected_axis[i] * projected_axis[j] / projected_norm - projection[i][j] for j in range(3)] for i in range(3)]


def verify_operator_laws(mode: base.M, axis: Axis) -> None:
    symbol = reflection_symbol(mode, axis)
    assert symbol is not None
    projection = projection_matrix(mode)
    assert symbol == [list(row) for row in zip(*symbol, strict=True)]
    assert reflection_symbol(base.neg(mode), axis) == symbol
    assert matrix_multiply(symbol, symbol) == projection
    assert all(sum(F(mode[i]) * symbol[i][j] for i in range(3)) == 0 for j in range(3))
    basis = [
        [base.c(1), base.c(), base.c()],
        [base.c(), base.c(1), base.c()],
        [base.c(), base.c(), base.c(1)],
    ]
    for value in basis:
        left = base.curl(mode, matrix_vector(symbol, value))
        right = matrix_vector(symbol, base.curl(mode, value))
        assert base.va(left, right) == [base.c(), base.c(), base.c()]


def state_precomputation(state: dict[base.M, base.V]):
    nonlinear = base.nonlinear(state)
    norms = {mode: base.hp(value, value)[0] for mode, value in state.items()}
    energy = F(1, 2) * sum(norms.values())
    dissipation = sum(base.n2(mode) * norms[mode] for mode in state)
    quartic_reserve = 2 * energy * dissipation
    base_a = sum((1 + base.n2(mode)) ** 3 * base.n2(mode) * norms[mode] for mode in state)
    base_c = sum((1 + base.n2(mode)) ** 3 * base.hp(state[mode], nonlinear[mode])[0] for mode in state)
    return nonlinear, quartic_reserve, base_a, base_c


def candidate_components(state: dict[base.M, base.V], precomputation, axis: Axis):
    nonlinear, quartic_reserve, base_a, base_c = precomputation
    correction_a = F(0)
    correction_c = F(0)
    for mode, value in state.items():
        symbol = reflection_symbol(mode, axis)
        if symbol is None:
            return None
        weight = F((1 + base.n2(mode)) ** 3)
        correction_a += weight * base.n2(mode) * base.hp(value, matrix_vector(symbol, value))[0]
        correction_c += weight * base.hp(value, matrix_vector(symbol, nonlinear[mode]))[0]
    return base_a, correction_a, quartic_reserve, base_c, correction_c


def candidate_components_precomputed(state, precomputation, symbols, axis):
    nonlinear, quartic_reserve, base_a, base_c = precomputation
    correction_a = F(0)
    correction_c = F(0)
    for mode, value in state.items():
        symbol = symbols[(axis, mode)]
        weight = F((1 + base.n2(mode)) ** 3)
        correction_a += weight * base.n2(mode) * base.hp(value, matrix_vector(symbol, value))[0]
        correction_c += weight * base.hp(value, matrix_vector(symbol, nonlinear[mode]))[0]
    return base_a, correction_a, quartic_reserve, base_c, correction_c


def favourable_margin(components, coupling: F) -> F:
    base_a, correction_a, quartic_reserve, base_c, correction_c = components
    corrected_a = base_a + coupling * correction_a
    corrected_c = base_c + coupling * correction_c
    return 4 * corrected_a * quartic_reserve - corrected_c * corrected_c


def corrected_coefficients(components, coupling: F):
    base_a, correction_a, quartic_reserve, base_c, correction_c = components
    return base_a + coupling * correction_a, quartic_reserve, base_c + coupling * correction_c, favourable_margin(components, coupling)


def canonical_axes(bound: int) -> list[Axis]:
    axes: list[Axis] = []
    for axis in product(range(-bound, bound + 1), repeat=3):
        if axis == (0, 0, 0):
            continue
        divisor = math.gcd(math.gcd(abs(axis[0]), abs(axis[1])), abs(axis[2]))
        if divisor != 1:
            continue
        if next(entry for entry in axis if entry) < 0:
            continue
        axes.append(axis)
    return axes


def analytic_axis_maximum(components):
    _, _, _, _, correction_c = components
    candidates = [F(-1), F(1)]
    if correction_c:
        base_a, correction_a, quartic_reserve, base_c, correction_c = components
        vertex = (4 * correction_a * quartic_reserve - 2 * base_c * correction_c) / (2 * correction_c * correction_c)
        if -1 <= vertex <= 1:
            candidates.append(vertex)
    return max((favourable_margin(components, coupling), coupling) for coupling in candidates)


def best_continuous_chart(state: dict[base.M, base.V], axes: list[Axis]):
    precomputation = state_precomputation(state)
    best = None
    for axis in axes:
        components = candidate_components(state, precomputation, axis)
        if components is None:
            continue
        margin, coupling = analytic_axis_maximum(components)
        candidate = (margin, axis, coupling, components)
        if best is None or candidate[0] > best[0]:
            best = candidate
    assert best is not None
    return best


def gaussian_state(scalars: tuple[base.C, base.C, base.C]):
    state: dict[base.M, base.V] = {}
    for mode, scalar in zip(base.POS, scalars, strict=True):
        value = base.vs(scalar, base.BASE[mode])
        state[mode] = value
        state[base.neg(mode)] = [base.cc(entry) for entry in value]
    return state


def signed_permutations():
    return list(product(permutations(range(3)), product((-1, 1), repeat=3)))


def transform_mode(mode: base.M, transform, scale: int = 1):
    permutation, signs = transform
    return tuple(scale * signs[i] * mode[permutation[i]] for i in range(3))


def transform_vector(value: base.V, transform):
    permutation, signs = transform
    return [base.cs(F(signs[i]), value[permutation[i]]) for i in range(3)]


def transform_state(state, transform, scale: int = 1):
    return {transform_mode(mode, transform, scale): transform_vector(value, transform) for mode, value in state.items()}


def dilate_state(state, scale: int):
    return {tuple(scale * coordinate for coordinate in mode): value for mode, value in state.items()}


def merge_states(*states):
    merged = {}
    for state in states:
        assert not set(merged).intersection(state)
        merged.update(state)
    return merged


def transverse_perturbation(state, coefficient: F):
    return {mode: base.va(value, [base.cs(coefficient, entry) for entry in base.curl(mode, value)]) for mode, value in state.items()}


def support_counterexample():
    p = (3, 5, -1)
    q = (5, 4, -4)
    k = (8, 9, -5)
    positive = {
        p: [base.c(23, -8), base.c(-12, 10), base.c(9, 26)],
        q: [base.c(-4, 16), base.c(22, -2), base.c(17, 18)],
        k: [base.c(1, 8), base.c(3, -1), base.c(7, 11)],
    }
    state = dict(positive)
    for mode, value in positive.items():
        state[base.neg(mode)] = [base.cc(entry) for entry in value]
    return p, q, k, state


def format_fraction(value: F) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def run():
    witness = base.state()
    axis = (0, 1, 1)
    coupling = F(-34_639, 39_764)
    coercivity_gap = F(1) - abs(coupling)
    assert coercivity_gap == F(5_125, 39_764)
    for mode in witness:
        verify_operator_laws(mode, axis)

    witness_components = candidate_components(witness, state_precomputation(witness), axis)
    assert witness_components is not None
    corrected_a, quartic_reserve, corrected_c, witness_margin = corrected_coefficients(witness_components, coupling)
    assert corrected_a == F(51_988_304_467, 9_941)
    assert quartic_reserve == 245_944
    assert corrected_c == F(-1_449_215_766, 9_941)
    assert witness_margin == F(506_330_689_890_146_637_116, 98_823_481)

    orbit_axes = [(0, 1, 1), (0, 1, -1), (1, 0, 1), (1, 0, -1), (1, 1, 0), (1, -1, 0)]
    fixed_support_symbols = {(chart, mode): reflection_symbol(mode, chart) for chart in orbit_axes for mode in witness}
    assert all(symbol is not None for symbol in fixed_support_symbols.values())

    balanced_total = balanced_dangerous = balanced_covered = 0
    for phases in product(range(4), repeat=3):
        for amplitudes in product((1, 2), repeat=3):
            state = base.state(phases, amplitudes)
            precomputation = state_precomputation(state)
            base_gap = precomputation[3] ** 2 - 4 * precomputation[2] * precomputation[1]
            balanced_total += 1
            if base_gap > 0:
                balanced_dangerous += 1
                best = max(favourable_margin(candidate_components_precomputed(state, precomputation, fixed_support_symbols, chart), coupling) for chart in orbit_axes)
                balanced_covered += int(best > 0)
    assert (balanced_total, balanced_dangerous, balanced_covered) == (512, 256, 256)

    gaussian_scalars = [base.c(real, imaginary) for real in range(-2, 3) for imaginary in range(-2, 3) if (real, imaginary) != (0, 0)]
    gaussian_total = gaussian_dangerous = gaussian_covered = 0
    for scalars in product(gaussian_scalars, repeat=3):
        state = gaussian_state(scalars)
        precomputation = state_precomputation(state)
        base_gap = precomputation[3] ** 2 - 4 * precomputation[2] * precomputation[1]
        gaussian_total += 1
        if base_gap > 0:
            gaussian_dangerous += 1
            best = max(favourable_margin(candidate_components_precomputed(state, precomputation, fixed_support_symbols, chart), coupling) for chart in orbit_axes)
            gaussian_covered += int(best > 0)
    assert (gaussian_total, gaussian_dangerous, gaussian_covered) == (13_824, 8_000, 8_000)

    transforms = signed_permutations()
    assert len(transforms) == 48
    for transform in transforms:
        state = transform_state(witness, transform)
        precomputation = state_precomputation(state)
        best = max(favourable_margin(candidate_components(state, precomputation, chart), coupling) for chart in orbit_axes if candidate_components(state, precomputation, chart) is not None)
        assert best > 0

    homogeneous_base_c = F(5_441_472)
    homogeneous_correction_c = F(68_712_192, 11)
    assert homogeneous_base_c + coupling * homogeneous_correction_c == 0

    dilation_coefficients = (103_416_122_250_981_553_072, 21_413_556_897_976_583_328, 1_703_070_875_420_836_824, 49_934_599_956_285_304, 12_151_798_599_249)
    positive_at_one = sum(dilation_coefficients[:4]) - dilation_coefficients[4]
    assert positive_at_one == 126_582_672_472_536_659_279
    for scale in (1, 2, 3, 4, 5, 8, 10, 20, 50, 100):
        state = dilate_state(witness, scale)
        components = candidate_components(state, state_precomputation(state), axis)
        assert components is not None
        x = F(scale * scale)
        polynomial_margin = F(4) * x / 98_823_481 * (F(dilation_coefficients[0]) * x**4 + F(dilation_coefficients[1]) * x**3 + F(dilation_coefficients[2]) * x**2 + F(dilation_coefficients[3]) * x - F(dilation_coefficients[4]))
        assert favourable_margin(components, coupling) == polynomial_margin
        assert polynomial_margin > 0

    for scales in ((1, 2), (1, 3), (1, 4), (2, 4), (1, 2, 4), (1, 5, 25)):
        state = merge_states(*(dilate_state(witness, scale) for scale in scales))
        precomputation = state_precomputation(state)
        best = max(favourable_margin(candidate_components(state, precomputation, chart), coupling) for chart in orbit_axes if candidate_components(state, precomputation, chart) is not None)
        assert best > 0

    for coefficient in (F(1, 100), F(-1, 100), F(1, 20), F(-1, 20), F(1, 10), F(-1, 10), F(1, 5), F(-1, 5)):
        state = transverse_perturbation(witness, coefficient)
        precomputation = state_precomputation(state)
        best = max(favourable_margin(candidate_components(state, precomputation, chart), coupling) for chart in orbit_axes if candidate_components(state, precomputation, chart) is not None)
        assert best > 0

    p, q, k, counterexample = support_counterexample()
    assert tuple(p[i] + q[i] for i in range(3)) == k
    for mode, value in counterexample.items():
        assert base.md(mode, value) == base.c()
        assert counterexample[base.neg(mode)] == [base.cc(entry) for entry in value]
    counterexample_precomputation = state_precomputation(counterexample)
    counterexample_gap = counterexample_precomputation[3] ** 2 - 4 * counterexample_precomputation[2] * counterexample_precomputation[1]
    assert counterexample_gap == 270_099_855_176_567_995_387_152

    axes_577 = canonical_axes(5)
    assert len(axes_577) == 577
    best_counterexample = best_continuous_chart(counterexample, axes_577)
    assert best_counterexample[0] == F(-43_765_141_812_998_928_078_607_884_222_016, 74_159_816_329)
    assert best_counterexample[1] == (3, 5, -4)
    assert best_counterexample[2] == -1
    assert best_counterexample[0] < 0

    return {
        "candidate": {"axis": axis, "coupling": format_fraction(coupling), "coercivityGap": format_fraction(coercivity_gap), "witnessA": format_fraction(corrected_a), "witnessB": format_fraction(quartic_reserve), "witnessC": format_fraction(corrected_c), "witnessMargin": format_fraction(witness_margin)},
        "inheritedBattery": {"balancedTotal": balanced_total, "balancedDangerous": balanced_dangerous, "balancedCovered": balanced_covered, "gaussianTotal": gaussian_total, "gaussianDangerous": gaussian_dangerous, "gaussianCovered": gaussian_covered, "signedSymmetries": len(transforms), "allPositiveIntegerDilationPolynomial": [str(value) for value in dilation_coefficients]},
        "optimizedCounterexample": {"p": p, "q": q, "k": k, "baseGap": format_fraction(counterexample_gap), "axesOptimized": len(axes_577), "bestMargin": format_fraction(best_counterexample[0]), "bestAxis": best_counterexample[1], "bestCoupling": format_fraction(best_counterexample[2])},
        "decision": {"modeLocalReflectionFamilyUniversallyClosed": False, "triadLevelDirectionCoherenceRequired": True},
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", type=Path)
    args = parser.parse_args()
    result = run()
    if args.json:
        args.json.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print("verified projected-axis matrix coherence: exact Hermitian/off-diagonal operator laws; witness margin positive; all 256 dangerous balanced and 8,000 dangerous Gaussian variants covered; symmetry, dilation, cluster, and transverse batteries covered; optimized resonant support defeats all 577 chart axes after exact continuous coupling optimization")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
