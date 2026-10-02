#!/usr/bin/env python3
"""Short-time finite-Galerkin ODE audit of the exact R823 sparse witness.

Reuses *existing* R233 mixed-helicity forcing-work machinery and the exact
sparse initial state in check_ns_r823_exact_sparse_reserve_witness.py.
Evolves the fully retained 26-mode radius-one cube with
    du_k/dt = projectedNonlinearity_k - |k|^2 u_k,
and integrates the correctly normalized instantaneous R815 rate:
    6 * (24 * realHermitianCommutatorCross - criticalProduction
         + criticalDissipation)
at nu=delta=1. R230 identifies product-rule work with the commutator
on the complete fixed-output fibre.

This is a numerical *diagnostic*, not verified interval integration or an
Agda R408 same-object counterexample. A negative integral, if reified,
would disprove the auxiliary universal B-reserve inequality, not NS.
"""
from __future__ import annotations
import json
import numpy as np
from scipy.integrate import solve_ivp
from check_ns_r823_exact_sparse_reserve_witness import SEEDS, MODES, dyadic_weight
from audit_mixed_helicity_forcing_work_round233 import (
    nonlinear_forcing, forcing_work
)

MODES_LIST = list(MODES)
COUNT = len(MODES_LIST)
INITIAL = {k: np.zeros(3, dtype=np.complex128) for k in MODES_LIST}
for k, v in SEEDS.items():
    value = np.array([complex(v[j]) for j in range(3)], dtype=np.complex128)
    INITIAL[k] = value
    INITIAL[tuple(-x for x in k)] = value.conjugate()


def rate(u):
    f = {k: nonlinear_forcing(MODES_LIST, u, k) for k in MODES_LIST}
    mixed_work, _mass = forcing_work(MODES_LIST, u)
    production = 2 * sum(
        float(dyadic_weight(k)) * np.vdot(u[k], f[k]).real
        for k in MODES_LIST
    )
    dissipation = sum(
        float(dyadic_weight(k)) * sum(x*x for x in k) *
        np.vdot(u[k], u[k]).real
        for k in MODES_LIST
    )
    # R692 Work.coherentWork is 2*realHermitianCross; R723 adds 12.\n    return 6 * (24 * mixed_work - production + dissipation)


def solve(horizon=0.002):
    calls = [0]
    def rhs(t, y):
        calls[0] += 1
        u = dict(zip(MODES_LIST, y[:3*COUNT].reshape(COUNT, 3)))
        f = {k: nonlinear_forcing(MODES_LIST, u, k) for k in MODES_LIST}
        derivative = np.array([
            f[k] - sum(x*x for x in k)*u[k] for k in MODES_LIST
        ]).reshape(-1)
        return np.concatenate([derivative, np.array([rate(u)+0j])])

    y0 = np.concatenate([
        np.array([INITIAL[k] for k in MODES_LIST]).reshape(-1),
        np.array([0j])
    ])
    result = solve_ivp(rhs, (0.0, horizon), y0, method="DOP853",
                       rtol=2e-11, atol=1e-12, dense_output=True)
    assert result.success

    samples = []
    for t in np.linspace(0, horizon, 9):
        y = result.sol(float(t))
        u = dict(zip(MODES_LIST, y[:3*COUNT].reshape(COUNT, 3)))
        reality_err = max(
            np.linalg.norm(u[tuple(-x for x in k)]-np.conj(u[k]))
            for k in MODES_LIST
        )
        transverse_err = max(
            abs(np.dot(k, u[k])) for k in MODES_LIST
        )
        samples.append({
            "time":float(t),"signed_rate":float(rate(u)),
            "integrated_rate":float(y[-1].real),
            "reality_error":float(reality_err),
            "transverse_error":float(transverse_err)
        })
    assert abs(samples[0]["signed_rate"] -
               (-19800-4248*2**0.5)) < 1e-7
    assert all(s["signed_rate"] < 0 for s in samples)
    assert samples[-1]["integrated_rate"] < 0
    assert max(s["reality_error"] for s in samples) < 1e-7
    assert max(s["transverse_error"] for s in samples) < 1e-7
    return {
        "schema":"ns_r823_short_time_finite_ode_v1",
        "status":"exploratory numerical, NOT rigorous integrated refutation",
        "horizon":horizon,"rhs_calls":calls[0],
        "initial_rate":samples[0]["signed_rate"],
        "terminal_integral":samples[-1]["integrated_rate"],
        "all_sampled_rates_negative":True,
        "samples":samples,
        "agda_r408_same_object_certified":False,
        "interval_arithmetic_certified":False,
        "clay_promotion":False
    }


if __name__ == "__main__":
    print(json.dumps(solve(),indent=2))
