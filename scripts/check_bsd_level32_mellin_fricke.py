#!/usr/bin/env python3
"""BSD level-32 CM analytic assay: real-axis positivity and Fricke-reduced Mellin.

This is a HIGH-PRECISION NUMERICAL REGRESSION, not a theorem, kernel
certificate, proof of Jacobi/eta inversion, or a definition of L(E,1).

f32(it) = eta(4it)^2 eta(8it)^2
        = exp(-2*pi*t) prod_{n>=1}
          (1-exp(-8*pi*n*t))^2(1-exp(-16*pi*n*t))^2.
Fricke (classical analytic source):
    f32(i/(32t)) = 32 t^2 f32(it).
Mellin (classical analytic source, original normalized newform):
    L(E,1) = 2*pi*integral_0^infinity f32(it)dt
           = 4*pi*integral_{1/sqrt(32)}^infinity f32(it)dt.

The last integral is STRICTLY POSITIVE once the eta product and
normalised level-32 newform/Mellin same-object identifications are
proved on the original Bishop carriers. Numerical agreement does not
replace that original theorem.

Requires mpmath; does not run CI or touch repo pins.
"""
from __future__ import annotations

import argparse
import json


def assay(dps: int = 65, terms: int = 110) -> dict:
    try:
        import mpmath as mp
    except ImportError as exc:
        raise SystemExit("BLOCKED: mpmath is needed for numeric assay") from exc
    if dps < 30 or terms < 30:
        raise ValueError("set dps>=30 and terms>=30")
    mp.mp.dps = dps
    def f(t):
        q = mp.exp(-2*mp.pi*t)
        y = q
        for n in range(1, terms+1):
            y *= (1-q**(4*n))**2*(1-q**(8*n))**2
        return y
    start = 1/mp.sqrt(32)
    # By Fricke symmetry, all evaluations of the integral are at t>=start.
    numeric_l1 = 4*mp.pi*mp.quad(f, [start, 1, 3, mp.inf])
    probes = [mp.mpf("0.04"), mp.mpf("0.14"),
              mp.mpf("0.24"), mp.mpf("0.75")]
    rel_errors = []
    for t in probes:
        left=f(1/(32*t))
        right=32*t*t*f(t)
        rel_errors.append(abs(left/right-1))
    no_zero_samples = all(f(t)>0 for t in probes+[start, mp.mpf(1)])
    # This is an external reference decimal, not used as a proof hypothesis.
    lmfdb_decimal=mp.mpf("0.65551438857302995261620989747277985342")
    match_error = abs(numeric_l1-lmfdb_decimal)
    return {
        "curve": "y^2=x^3-x (LMFDB 32.a3)",
        "newform": "eta(4z)^2 eta(8z)^2",
        "precision_decimal_digits": dps,
        "finite_q_product_terms": terms,
        "fricke_fixed_point": mp.nstr(start, 24),
        "mellin_one_tail_value": mp.nstr(numeric_l1, dps-5),
        "max_fricke_relative_error": mp.nstr(max(rel_errors), 12),
        "sampled_eta_integrand_positive": bool(no_zero_samples),
        "external_lmfdb_reference_error": mp.nstr(match_error, 12),
        "numerical_assay_pass": bool(
            no_zero_samples and max(rel_errors) < mp.mpf("1e-35")
            and match_error < mp.mpf("1e-35")),
        "infinite_eta_identity_formalized": False,
        "bishop_mellin_identification_formalized": False,
        "agda_or_lean_kernel_accepted": False,
    }


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dps",type=int,default=65)
    parser.add_argument("--terms",type=int,default=110)
    args=parser.parse_args()
    data=assay(args.dps,args.terms)
    print(json.dumps(data,indent=2))
    if not data["numerical_assay_pass"]:
        raise SystemExit("FAILED: inspect finite truncation error & precision")


if __name__=="__main__":
    main()
