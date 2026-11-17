#!/usr/bin/env python3
"""Source-bounded Eq(7) audit of Ramirez-Galindo et al 2024.

Source-original owner: A. D. Ramirez-Galindo et al, Revista Mexicana de Fisica
70 (2024), e030901, DOI 10.31349/RevMexFis.70.030901.
Their Eq (7) B = curl A gives flux density B, not the spatial derivative
tensor grad B or the distinct scalar-magnitude gradient grad |B|.
The counterexample and checker are DASHI-authored under Johl Brown's
investigative direction, assisted by OpenAI ChatGPT. No coil data acquired.

Use an exactly differentiated affine vector potential A(r) = c + M r:
  curl A = (M_zy - M_yz, M_xz - M_zx, M_yx - M_xy)
which is spatially CONSTANT for any affine M, thus its Jacobian is zero.
A=(0,x,0) gives curl A=(0,0,1), nonzero, grad curl A = zero.
All coordinates are symbolic; a physical A has units T*m, B T, grad B T/m.
This is an algebraic discriminator, not a numerical experiment.
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction as F
from itertools import product

ZERO = F(0)
Z3 = (ZERO, ZERO, ZERO)
Z9 = (Z3, Z3, Z3)
EXACT_SOURCE = {
    "authors": "Ramirez-Galindo et al.",
    "doi": "10.31349/RevMexFis.70.030901",
    "year_of_issue": 2024,
    "equation": 7,
    "source_url": "https://www.scielo.org.mx/scielo.php?pid=S0035-001X2024000300006&script=sci_arttext",
    "published_operator": "B = curl(A)",
    "following_prose": "This expression represents the calculation of the magnetic field gradient.",
}

def affine_curl(m: tuple[tuple[F, F, F], ...]) -> tuple[F, F, F]:
    """Exact first spatial derivative, row output component, column coordinate."""
    if len(m) != 3 or any(len(row) != 3 for row in m):
        raise ValueError("expected 3x3 Cartesian Jacobian of vector potential")
    return (m[2][1] - m[1][2], m[0][2] - m[2][0], m[1][0] - m[0][1])

def affine_b_gradient(m: tuple[tuple[F, F, F], ...]) -> tuple[tuple[F, F, F], ...]:
    """Jacobian of the CONSTANT curl of an affine vector potential."""
    affine_curl(m)
    return Z9

def scaled_symmetric_gauge(m: tuple[tuple[F, F, F], ...],
                           h: tuple[tuple[F, F, F], ...]):
    """Add grad chi for chi=(1/2) r.T h r, with symmetric h."""
    if any(h[i][j] != h[j][i] for i in range(3) for j in range(3)):
        raise ValueError("gauge Hessian must be symmetric")
    return tuple(tuple(m[i][j] + h[i][j] for j in range(3)) for i in range(3))

def witness() -> dict:
    m = ((ZERO, ZERO, ZERO), (F(1), ZERO, ZERO), Z3)
    b = affine_curl(m)
    g = affine_b_gradient(m)
    if b != (ZERO, ZERO, F(1)) or g != Z9:
        raise AssertionError("affine A=(0,x,0) counterexample failed")
    h = ((F(2), F(1), ZERO), (F(1), F(3), ZERO), (ZERO, ZERO, F(4)))
    if affine_curl(scaled_symmetric_gauge(m, h)) != b:
        raise AssertionError("quadratic gauge must not change B")
    return {
        "original_source": EXACT_SOURCE,
        "symbolic_vector_potential": ["0", "x", "0"],
        "curl_A_T": [str(z) for z in b],
        "jacobian_B_T_per_m": [[str(z) for z in row] for row in g],
        "grad_magnitude_B_T_per_m": ["0", "0", "0"],
        "nonzero_B_with_zero_gradient": True,
        "grad_B_is_rank_two_not_curl_A_vector": True,
        "gauge_invariance_checked": True,
        "mathematical_correction_not_retraction_of_physical_measurements": True,
        "agda_kernel_checked": False,
        "real_2024_coil_data_analysed": False,
    }

def self_test() -> dict:
    count = 0
    # Test all 3^6 integer coefficients of an affine potential with only
    # x,y variable dependence; each curl is uniform, including nonzero cases.
    for cells in product((-1, 0, 1), repeat=6):
        m = tuple((F(cells[2*i]), F(cells[2*i+1]), ZERO) for i in range(3))
        b = affine_curl(m)
        assert affine_b_gradient(m) == Z9
        assert b == (m[2][1], -m[2][0], m[1][0] - m[0][1])
        count += 1
    for bad in ((Z3,), (Z3, Z3, (ZERO,)), ()):
        try:
            affine_curl(bad)
        except ValueError:
            count += 1
        else:
            raise AssertionError("malformed affine Jacobian accepted")
    h = ((ZERO, F(1), ZERO), (ZERO, ZERO, ZERO), Z3)
    try:
        scaled_symmetric_gauge(Z9, h)
    except ValueError:
        count += 1
    else:
        raise AssertionError("nonsymmetric gauge accepted")
    assert count == 733
    witness()
    return {"exact_affine_cases_passed": 729,
            "invalid_structures_rejected": 4,
            "total_cases": count,
            "identity_B_is_gradient_refuted_by_counterexample": True,
            "no_source_raw_field_or_experiment_claim": True}

def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--self-test", action="store_true")
    args = p.parse_args()
    result = witness()
    if args.self_test:
        result["self_test"] = self_test()
    print(json.dumps(result, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
