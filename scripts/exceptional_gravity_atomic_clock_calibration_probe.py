from __future__ import annotations

from fractions import Fraction
from itertools import product
import math
import sympy as sp

CS133_HZ = 9_192_631_770
C_M_PER_S = 299_792_458
# Bothwell--Ye public prediction in fractional-frequency gradient per mm.
BOTHWELL_THEORY_PER_MM = 1.09e-19
BOTHWELL_CORRECTED_PER_MM = 0.98e-19
BOTHWELL_CORRECTED_SIGMA_PER_MM = 0.23e-19

x, y, z, eps = sp.symbols("x y z eps", real=True)
phi = sp.Rational(1, 108) * (
    54*x**2*y**2*z**2
    - 36*x**2*y**2
    - 9*x**2*z**2
    + 6*x**2
    - 18*x*y**2*z
    + 3*x*z
    - 36*y**2*z**2
    - 12*y**2
    + 6*z**2
    + 20
)


def gradient_log_omega(unit_amplitude=True):
    omega = 1 + phi if unit_amplitude else 1 + eps * phi
    return tuple(sp.simplify(sp.diff(sp.log(omega), v)) for v in (x, y, z))


def verify():
    grad = gradient_log_omega(True)
    samples = []
    for point in product((-1, 0, 1), repeat=3):
        subs = dict(zip((x, y, z), point))
        values = tuple(sp.simplify(g.subs(subs)) for g in grad)
        samples.append((point, values))

    vertical_point, vertical_grad = max(samples, key=lambda item: abs(float(item[1][2])))
    assert vertical_point in ((0, -1, -1), (0, 1, 1))
    vertical_exact = abs(vertical_grad[2])
    assert vertical_exact == sp.Rational(30, 43)
    chosen_subs = dict(zip((x, y, z), vertical_point))
    assert sp.simplify(phi.subs(chosen_subs)) == sp.Rational(-11, 54)
    assert abs(sp.simplify(sp.diff(phi, z).subs(chosen_subs))) == sp.Rational(5, 9)

    # Candidate SI map used only as a falsifier: one lattice edge is the light
    # travel distance during one Cs-133 SI-defining transition period.
    edge_m = Fraction(C_M_PER_S, CS133_HZ)
    edge_mm = float(edge_m * 1000)
    unit_vertical_per_mm = float(vertical_exact) / edge_mm
    ratio_to_theory = unit_vertical_per_mm / BOTHWELL_THEORY_PER_MM
    assert ratio_to_theory > 1e17

    # Weak-amplitude family Omega_eps = 1 + eps*phi. At the selected point,
    # |d_z log Omega_eps| = eps*(5/9)/(1-eps*11/54).
    target_per_step = BOTHWELL_THEORY_PER_MM * edge_mm
    target = sp.Float(target_per_step, 50)
    epsilon_solution = sp.solve(
        sp.Eq(eps * sp.Rational(5, 9) / (1 - eps * sp.Rational(11, 54)), target),
        eps,
    )[0]
    epsilon_float = float(epsilon_solution)
    assert 6.3e-18 < epsilon_float < 6.5e-18

    corrected_target = BOTHWELL_CORRECTED_PER_MM * edge_mm
    corrected_eps = sp.solve(
        sp.Eq(
            eps * sp.Rational(5, 9) / (1 - eps * sp.Rational(11, 54)),
            sp.Float(corrected_target, 50),
        ),
        eps,
    )[0]

    return {
        "candidate_edge_m": edge_m,
        "candidate_edge_mm": edge_mm,
        "max_vertical_point": vertical_point,
        "phi_at_max_vertical": sp.Rational(-11, 54),
        "dphi_dz_at_max_vertical_abs": sp.Rational(5, 9),
        "dlogomega_dz_unit_abs": sp.Rational(30, 43),
        "unit_amplitude_vertical_gradient_per_mm": unit_vertical_per_mm,
        "bothwell_theory_gradient_per_mm": BOTHWELL_THEORY_PER_MM,
        "unit_over_theory_ratio": ratio_to_theory,
        "epsilon_to_match_theory": epsilon_float,
        "epsilon_to_match_corrected_central": float(corrected_eps),
        "corrected_sigma_per_mm": BOTHWELL_CORRECTED_SIGMA_PER_MM,
    }


if __name__ == "__main__":
    for key, value in verify().items():
        print(f"{key}: {value}")
