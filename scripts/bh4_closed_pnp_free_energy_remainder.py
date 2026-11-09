"""Closed grounded reactive-PNP exact free-energy remainder identity.

Assistant-authored mathematical verification assistance using established
finite-volume thermodynamics on user-origin DASHI 369 geometry.
This is a finite-dimensional analytic identity, not Agda kernel acceptance,
original Rhea kinetics, physiological evidence, or a proof of root existence.

For any strictly positive before/after charts:
 F(after)-F(before) =
 dt*(transport_power + reaction_power)
 + h**3 * sum(mu_after * implicit_residual)
 - chemical_bregman_gap - electrostatic_bregman_gap.

The gaps are nonnegative when RT>0 and the grounded Poisson matrix is SPD.
At an EXACT implicit root the residual term is zero; with detailed balance,
nonnegative diffusivity and blocking material boundaries the powers are <=0.
"""
import numpy as np
from reactive_pnp_369 import (
    poisson, free_energy, vector_rhs, dissipation_diagnostics,
)


def remainder_receipt(before, after, dt, model):
    c0 = np.asarray(before, dtype=float)
    c1 = np.asarray(after, dtype=float)
    if c0.shape != (27, len(model.z)) or c1.shape != c0.shape:
        raise ValueError("same complete original 27-site concentration chart required")
    if not np.all(np.isfinite(c0)) or not np.all(np.isfinite(c1)) or np.any(c0 <= 0) or np.any(c1 <= 0):
        raise ValueError("finite strictly positive before/after states required")
    if not np.isfinite(dt) or dt <= 0:
        raise ValueError("positive finite timestep required")
    phi0, phi1 = poisson(c0, model), poisson(c1, model)
    mu1 = (model.standard_mu[None, :] + model.RT*np.log(c1)
           + model.F*phi1[:, None]*model.z[None, :])
    defect = c1 - c0 - dt*vector_rhs(c1, model, phi1)
    chemical_gap = (model.h**3 * model.RT *
        float(np.sum(c0*np.log(c0/c1) - c0 + c1)))
    drho = model.F*((c0-c1)@model.z)
    electrostatic_gap = (0.5*model.h**3*
        float(np.dot(drho, phi0-phi1)))
    power = dissipation_diagnostics(c1, phi1, model)
    energy_change = float(free_energy(c1, phi1, model)
                          - free_energy(c0, phi0, model))
    residual_work = model.h**3 * float(np.sum(mu1*defect))
    residual_work_bound = (model.h**3 * float(np.sum(np.abs(mu1)))
                           * float(np.max(np.abs(defect))))
    reconstructed = (dt*(power["transport_power"]+power["reaction_power"])
                     + residual_work - chemical_gap - electrostatic_gap)
    if not np.all(np.isfinite([energy_change,reconstructed,chemical_gap,
                              electrostatic_gap,residual_work])):
        raise ValueError("nonfinite convexity identity receipt")
    # Negative roundoff-scale gaps are not silently clamped to zero.
    return {
        "energy_change": energy_change,
        "reconstructed_change": float(reconstructed),
        "identity_defect": float(energy_change-reconstructed),
        "chemical_bregman_gap": float(chemical_gap),
        "electrostatic_bregman_gap": float(electrostatic_gap),
        "residual_work": float(residual_work),
        "residual_work_absolute_bound": float(residual_work_bound),
        "energy_change_upper_bound": float(dt*(power["transport_power"]+power["reaction_power"]) + residual_work_bound),
        "implicit_residual_max": float(np.max(np.abs(defect))),
        "root_existence_proven": False,
        "original_source_parameters_authenticated": False,
        "agda_kernel_checked": False,
        **power,
    }
