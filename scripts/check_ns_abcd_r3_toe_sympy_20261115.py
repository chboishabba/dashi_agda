#!/usr/bin/env python3
"""Exact symbolic cross-checks for DASHI NS Lane A/R3, Lane B/R854,
and OpenAI R3PressureKernel -- NOT an Agda/Lean kernel or a Clay proof.

Original mathematical sources: classical spherical coordinates and Lebesgue
integration; C. Fefferman's Clay NS description; OpenAI
NavierStokesAndEuler@f9e8bc5b38b6e212696e8a30e3e91517af887bbd
NavierStokes/R3PressureKernel.lean; DASHI Golden Agda owners:
NSWholeSpaceR3RadialFactorBudgetExact and
NSTriadKNR650Rational345LipschitzIntegralRound854Exact.

The radial equality is a reference identity for standard Euclidean volume,
not proof of a periodic pressure kernel, the original fluid's Lp estimates,
second-moment source budget, or an R3/T3 physical same-object transport.
"""
import json
import sympy as sp


def main():
    r, R, q, nu, G, Q = sp.symbols("r R q nu G Q", positive=True, real=True)
    # K_R(r) = r^(-3)*min(r/R,1).  Near 0 K_R = r^-2/R;
    # at infinity K_R=r^-3.  This matches upstream R3PressureKernel.
    inner = sp.simplify(R**(-sp.Rational(4, 3)) *
                        sp.integrate(r**(-sp.Rational(2, 3)), (r, 0, R)))
    outer = sp.integrate(r**(-2), (r, R, sp.oo))
    moment = sp.simplify(4 * sp.pi * (inner + outer))
    assert sp.simplify(inner - 3/R) == 0
    assert sp.simplify(outer - 1/R) == 0
    assert sp.simplify(moment - 16*sp.pi/R) == 0
    # The mathematical standard L^(4/3) norm is the 3/4 power of its moment.
    assert sp.simplify((moment / (16*sp.pi/R))**sp.Rational(3, 4)) == 1
    assert sp.simplify(moment.subs(R, sp.Rational(1, 4)) /
                       moment.subs(R, 1)) == 4

    # Golden R3 source q=|xi|^2, a=nu*q.  Radial r^2 density +
    # projected Gram q + missing physical 2nd moment q cancel a^-3.
    paid = sp.cancel(q * (nu*q)**(-3) * (q*G) * (q*Q))
    assert sp.simplify(paid - G*Q/nu**3) == 0
    unprovided_second_moment = sp.cancel(q * (nu*q)**(-3) * (q*G) * Q)
    assert sp.simplify(unprovided_second_moment - G*Q/(nu**3*q)) == 0
    # Without the second q, q=r^2 leaves a divergent integral at the origin.
    assert sp.integrate(r**-2, (r, 0, 1)) == sp.oo
    # If G*Q stays constant, the paid bound is not integrable globally.
    assert sp.integrate(sp.Integer(1), (r, 0, sp.oo)) == sp.oo

    # Existing R854 selected exact rational arithmetic, NOT a Galerkin flow.
    r0 = -sp.Rational(28273644, 125)
    L = sp.Integer(391309593930357307785216)
    T = sp.Rational(226189, 3938540454339300631433585885184)
    terminal = sp.factor(r0 + L*T)
    integrated_affine = sp.factor(r0*T + L*T*T/2)
    assert T > 0 and L > 0 and terminal < 0 and integrated_affine < 0
    assert sp.simplify(L*T - sp.Rational(226189, 10065024)) == 0

    print(json.dumps({
        "result": "PASS",
        "euclidean_R3_pressure_kernel_moment": "16*pi/R",
        "near_radial_moment_contribution": "12*pi/R",
        "far_radial_moment_contribution": "4*pi/R",
        "pressure_R_to_quarter_moment_ratio": 4,
        "DASHI_A_radial_budget": "G*Q/nu**3",
        "omitting_physical_second_moment_q": "G*Q/(nu**3*q)",
        "origin_nonintegrability_control": True,
        "far_majorant_integrability_remains_open": True,
        "R854_affine_terminal": str(terminal),
        "R854_affine_integral_upper": str(integrated_affine),
        "sympy_version": sp.__version__,
        "lean_kernel_checked": False,
        "agda_kernel_checked": False,
        "same_object_physical_weld": False,
        "clay_theorem_proved": False
    }, sort_keys=True))


if __name__ == "__main__":
    main()
