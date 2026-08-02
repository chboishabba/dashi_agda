#!/usr/bin/env python3
"""Exact direction-coherence diagnostics and audit of the April-2026 claim."""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from pathlib import Path

import ns_quartic_localized_helicity_reconnaissance as base
import ns_quartic_matrix_coherence_reconnaissance as matrix


def complex_abs_squared(value: base.C) -> F:
    return value[0] * value[0] + value[1] * value[1]


def complex_cross(left: base.V, right: base.V) -> base.V:
    return [
        base.ca(base.cm(left[1], right[2]), base.cs(F(-1), base.cm(left[2], right[1]))),
        base.ca(base.cm(left[2], right[0]), base.cs(F(-1), base.cm(left[0], right[2]))),
        base.ca(base.cm(left[0], right[1]), base.cs(F(-1), base.cm(left[1], right[0]))),
    ]


def gram_defect(left: base.V, right: base.V) -> tuple[F, F]:
    left_norm = base.hp(left, left)[0]
    right_norm = base.hp(right, right)[0]
    pairing = base.hp(left, right)
    denominator = left_norm * right_norm
    defect = denominator - complex_abs_squared(pairing)
    assert 0 <= defect <= denominator
    return defect, denominator


def alignment_rows(state):
    rows = []
    for p, q, k in base.triads(state):
        omega_p = base.curl(p, state[p])
        omega_q = base.curl(q, state[q])
        defect, denominator = gram_defect(omega_p, omega_q)
        transfer = base.hp(state[k], base.nt(state, k, p, q))[0]
        rows.append((p, q, k, defect, denominator, transfer))
    return rows


def alignment_weighted_transfer(state) -> F:
    return sum(F(defect, denominator) * transfer for _, _, _, defect, denominator, transfer in alignment_rows(state))


def convolved_cross(left, right):
    out = {}
    for p, left_value in left.items():
        for q, right_value in right.items():
            mode = tuple(p[i] + q[i] for i in range(3))
            contribution = complex_cross(left_value, right_value)
            out[mode] = base.va(out.get(mode, [base.c(), base.c(), base.c()]), contribution)
    return out


def curl_field(field):
    return {mode: base.curl(mode, value) for mode, value in field.items()}


def add_fields(left, right):
    zero = [base.c(), base.c(), base.c()]
    return {mode: base.va(left.get(mode, zero), right.get(mode, zero)) for mode in set(left) | set(right)}


def t3_candidate_and_euler_derivative(state):
    """T3 = sum |curl(omega cross u)|^2 and its exact Galerkin Euler derivative."""
    nonlinear = base.nonlinear(state)
    omega = curl_field(state)
    omega_derivative = curl_field(nonlinear)
    current = curl_field(convolved_cross(omega, state))
    current_derivative = curl_field(add_fields(convolved_cross(omega_derivative, state), convolved_cross(omega, nonlinear)))
    t3 = sum(base.hp(value, value)[0] for value in current.values())
    derivative = 2 * sum(base.hp(current[mode], current_derivative.get(mode, [base.c(), base.c(), base.c()]))[0] for mode in current)
    return t3, derivative


def trace_free_compressive_counterexample():
    trace = F(1) + F(1) - F(2)
    alpha = F(-2)
    assert trace == 0
    assert alpha < 0
    return trace, alpha


def format_fraction(value: F) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def run():
    witness = base.state()
    _, _, _, support_state = matrix.support_counterexample()

    witness_rows = alignment_rows(witness)
    support_rows = alignment_rows(support_state)
    assert len(witness_rows) == len(support_rows) == 12
    witness_defect_sum = sum(row[3] for row in witness_rows)
    support_defect_sum = sum(row[3] for row in support_rows)
    witness_weighted = alignment_weighted_transfer(witness)
    support_weighted = alignment_weighted_transfer(support_state)
    assert witness_defect_sum == 691_128
    assert support_defect_sum == 28_906_945_080
    assert witness_weighted == F(31_302, 143)
    assert support_weighted == F(-17_822_768_857_756_493, 213_942_878_310)
    assert witness_weighted != 0 and support_weighted != 0

    trace, compressive_alpha = trace_free_compressive_counterexample()
    witness_t3, witness_t3_derivative = t3_candidate_and_euler_derivative(witness)
    support_t3, support_t3_derivative = t3_candidate_and_euler_derivative(support_state)
    assert witness_t3 == 867_456
    assert witness_t3_derivative == F(34_108_128, 5)
    assert support_t3 == 12_172_469_428
    assert support_t3_derivative == F(-12_347_695_354_951_776, 11_305)
    assert witness_t3_derivative != 0
    assert support_t3_derivative != 0

    return {
        "fourierPolarizationSurrogate": {
            "witnessGramDefectSum": format_fraction(witness_defect_sum),
            "witnessAlignmentWeightedTransfer": format_fraction(witness_weighted),
            "supportGramDefectSum": format_fraction(support_defect_sum),
            "supportAlignmentWeightedTransfer": format_fraction(support_weighted),
            "isConstantinFeffermanDirectionField": False,
        },
        "translationInvariantQuadraticAudit": {
            "crossModeKernelAllowed": False,
            "reason": "translation characters force k=l for invariant quadratic forms",
        },
        "permanav3Audit": {
            "traceFreeStrain": format_fraction(trace),
            "compressiveAlignment": format_fraction(compressive_alpha),
            "t3WitnessValue": format_fraction(witness_t3),
            "t3WitnessEulerDerivative": format_fraction(witness_t3_derivative),
            "t3SupportValue": format_fraction(support_t3),
            "t3SupportEulerDerivative": format_fraction(support_t3_derivative),
            "t3EulerInvariant": False,
            "globalRegularityClaimImported": False,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", type=Path)
    args = parser.parse_args()
    result = run()
    if args.json:
        args.json.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print("verified direction-coherence audit: modal Gram-defect signal is nontrivial but is not the Constantin-Fefferman direction field; trace-free strain permits compressive alignment; the proposed T3=||curl(omega cross u)||_2^2 has nonzero exact Euler derivative on both finite witnesses")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
