#!/usr/bin/env python3
"""Exact integer three-mode aliasing and balanced-trit codec diagnostic.

Physics: quadratic Fourier convolutions in pseudo-spectral NS require integer
mode sums before folding into sampled residues. The exact mode support of
[-1,0,+1]^2 is [-2,-1,0,+1,+2]. Folding onto N=3 aliases +2->-1 and
-2->+1. A 5-point grid resolves this *particular* finite product, but is not
a convergence proof, a Navier-Stokes solver, an optical-clock simulation or
a source of experimental findings.

Prior art: Orszag/Patterson; Lambert, Reneuve, Augier, arXiv:2603.08892.
Original DASHI owners: VerifiedFiniteTritCoder, BinaryBalancedTernary-
SubcarrierExact, and NSIntegerFourierLattice (Z^3).
"""
from __future__ import annotations

import argparse
from itertools import product
from collections import defaultdict
from fractions import Fraction
import json

MODES = (-1, 0, 1)
CODEC = {-1: (0, 0), 0: (0, 1), 1: (1, 0)}
DECODE = {(0, 0): -1, (0, 1): 0, (1, 0): 1, (1, 1): None}
BINARY_IN_TERNARY = {False: -1, True: 1}


def centered_mod(k: int, n: int) -> int:
    if n % 2 != 1 or n < 3:
        raise ValueError("odd grid n>=3 required")
    return (k + n // 2) % n - n // 2


def exact_quadratic_product(amplitudes: tuple[int, int, int]) -> dict[int, int]:
    """Fourier coefficients of u*u, exact integer convolution."""
    result: dict[int, int] = defaultdict(int)
    for a, av in zip(MODES, amplitudes):
        for b, bv in zip(MODES, amplitudes):
            result[a+b] += av * bv
    return dict(result)


def sampled_quadratic_product(amplitudes: tuple[int, int, int], n: int) -> dict[int, int]:
    """Evaluate a pointwise product on n periodic samples: coefficient folding."""
    result: dict[int, int] = defaultdict(int)
    for k, value in exact_quadratic_product(amplitudes).items():
        result[centered_mod(k, n)] += value
    return dict(result)


def kept_modes(amplitudes: tuple[int, int, int], grid: int):
    full = exact_quadratic_product(amplitudes)
    sampled = sampled_quadratic_product(amplitudes, grid)
    return (
        tuple(full.get(m, 0) for m in MODES),
        tuple(sampled.get(m, 0) for m in MODES),
    )



def three_axis_27_mode_pair_audit() -> dict:
    """Exact C3^3-vs-Z^3 incidence cut: 27² pairs in a {-1,0,1}^3 cube."""
    cube = tuple(product(MODES, repeat=3))
    pairs = 0
    out_of_cube = 0
    padded_axis_folding_errors = 0
    exemplar = {}
    for p, q in product(cube, repeat=2):
        pairs += 1
        k = tuple(a + b for a, b in zip(p, q))
        wrap3 = tuple(centered_mod(v, 3) for v in k)
        wrap5 = tuple(centered_mod(v, 5) for v in k)
        if any(abs(v) > 1 for v in k):
            out_of_cube += 1
        if wrap5 != k:
            padded_axis_folding_errors += 1
        if p == (1, 0, 0) and q == (1, 0, 0):
            exemplar = {"p": list(p), "q": list(q),
                        "integer_sum": list(k), "folded_C3_cubed": list(wrap3)}
    assert len(cube) == 27
    assert pairs == 729
    assert out_of_cube == 386
    assert padded_axis_folding_errors == 0
    assert exemplar["integer_sum"] == [2, 0, 0]
    assert exemplar["folded_C3_cubed"] == [-1, 0, 0]
    return {
        "spatial_mode_labels": len(cube),
        "ordered_quadratic_mode_pairs": pairs,
        "pairs_with_at_least_one_component_outside_retained_cube": out_of_cube,
        "pairs_entirely_inside_retained_cube": pairs - out_of_cube,
        "five_grid_each_axis_mode_wrap_errors": padded_axis_folding_errors,
        "example": exemplar,
        "physical_NS_vector_projection_claimed": False,
        "NS_time_evolution_or_Clay_claimed": False,
    }



def exact_two_mode_leray_aliasing_audit() -> dict:
    """A nonzero, divergence-free, quadratic NS Fourier-mode test.

    Only the symmetric convective Fourier coefficient and algebraic
    Leray projector P_k=I-kk^T/|k|² are modelled. The common complex
    Fourier factor i is omitted. No NS velocity solution is constructed.
    """
    p, q = (1, 0, 0), (1, 1, 0)
    a, b = (0, 1, 0), (1, -1, 0)

    def dot(v, w):
        return sum(x*y for x, y in zip(v, w))

    def add(v, w):
        return tuple(x+y for x, y in zip(v, w))

    def leray(k, v):
        k2 = dot(k, k)
        if k2 == 0:
            raise ValueError("Leray projector at zero wavevector is not selected")
        contraction = Fraction(dot(k, v), k2)
        return tuple(Fraction(x) - contraction*y for x, y in zip(v, k))

    assert dot(p, a) == 0
    assert dot(q, b) == 0
    k = add(p, q)
    aliased = tuple(centered_mod(x, 3) for x in k)
    # Ordered p,q and q,p contributions to (u·∇)u, up to common i.
    convective = tuple(dot(a, q)*b_i + dot(b, p)*a_i
                       for a_i, b_i in zip(a, b))
    true_projected = leray(k, convective)
    aliased_projected = leray(aliased, convective)
    assert k == (2, 1, 0)
    assert aliased == (-1, 1, 0)
    assert convective == (1, 0, 0)
    assert true_projected == (Fraction(1, 5), Fraction(-2, 5), Fraction(0))
    assert aliased_projected == (Fraction(1, 2), Fraction(1, 2), Fraction(0))
    assert true_projected != aliased_projected
    return {
        "p": list(p), "q": list(q),
        "transverse_p_amplitude": list(a),
        "transverse_q_amplitude": list(b),
        "true_integer_output_k": list(k),
        "folded_three_grid_output_k": list(aliased),
        "symmetrized_input_nonlinearity_up_to_i": list(convective),
        "leray_at_true_k": list(map(str, true_projected)),
        "leray_at_folded_k": list(map(str, aliased_projected)),
        "different": True,
        "full_NS_equations_or_time_evolution_solved": False,
        "uniform_cutoff_estimate_established": False,
    }


def audit() -> dict:
    assert all(DECODE[CODEC[m]] == m for m in MODES)
    assert DECODE[(1, 1)] is None
    assert BINARY_IN_TERNARY[False] == -1
    assert BINARY_IN_TERNARY[True] == 1
    assert all(abs(a+b) <= 2 for a,b in product(MODES, repeat=2))
    assert centered_mod(2, 3) == -1
    assert centered_mod(-2, 3) == 1
    assert centered_mod(2, 5) == 2
    assert centered_mod(-2, 5) == -2

    total = 0
    aliased_three = 0
    mismatched_five = 0
    representative = {}
    for v in product(MODES, repeat=3):
        total += 1
        exact, coarse = kept_modes(v, 3)
        exact_five, padded = kept_modes(v, 5)
        assert exact == exact_five
        if exact != coarse:
            aliased_three += 1
        if exact != padded:
            mismatched_five += 1
        if v == (0, 0, 1):
            representative = {
                "input_modes_minus_zero_plus": list(v),
                "exact_retained": list(exact),
                "folded_three_point_retained": list(coarse),
                "padded_five_point_retained": list(padded),
                "untruncated_coeff_plus_two": exact_quadratic_product(v)[2],
            }
    assert total == 27
    assert aliased_three == 24
    assert mismatched_five == 0
    assert representative["exact_retained"] == [0, 0, 0]
    assert representative["folded_three_point_retained"] == [1, 0, 0]
    return {
        "scope": "finite exact quadratic convolution for balanced coefficients",
        "original_N": 3,
        "fully_product_resolving_N": 5,
        "balanced_input_profiles": total,
        "three_point_profiles_with_alias_in_kept_modes": aliased_three,
        "five_point_profiles_with_alias_in_kept_modes": mismatched_five,
        "codec_roundtrip_for_all_three_labels": True,
        "reserved_binary_codeword_rejected": True,
        "binary_subcarrier_uses_only_nonzero_modes": True,
        "example": representative,
        "three_axis_mode_pair_audit": three_axis_27_mode_pair_audit(),
        "two_mode_divergence_free_leray_audit": exact_two_mode_leray_aliasing_audit(),
        "ns_physical_model_realised": False,
        "ns_clay_or_qg_proved": False,
        "r2p2_optical_clock_measured": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pretty", action="store_true", help="indented audit JSON")
    args = parser.parse_args()
    print(json.dumps(audit(), sort_keys=True, indent=2 if args.pretty else None))


if __name__ == "__main__":
    main()
