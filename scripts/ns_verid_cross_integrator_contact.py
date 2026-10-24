#!/usr/bin/env python3
"""NS finite twin cross-integrator contact: RK4 versus SciPy DOP853.

Both solvers share the canonical finite Fourier RHS; this tests independent
time integrators, not independent spatial discretisations or physical truth.
"""
from __future__ import annotations
import argparse, hashlib, json, sys
from pathlib import Path
import numpy as np
from scipy.integrate import solve_ivp
from ns_periodic_galerkin_core import (
    make_geometry, random_state, rhs, rk4_step, total_energy,
    weighted_five_halves, vorticity_fourier_l1, project_state, enforce_reality
)

def digest(o):
    return hashlib.sha256(json.dumps(o, sort_keys=True, separators=(',', ':')).encode()).hexdigest()

def evaluate(seed=101, cutoff=2, dt=0.002, steps=8, viscosity=1.0, rtol=1e-9, atol=1e-11):
    if cutoff < 1 or steps < 1 or dt <= 0 or viscosity <= 0:
        raise ValueError('invalid cutoff, steps, timestep or viscosity')
    g = make_geometry(cutoff, max_shell=max(2, cutoff.bit_length()))
    initial = random_state(g, seed, energy=1.)
    rk = initial.copy()
    for _ in range(steps):
        rk = rk4_step(g, rk, dt, viscosity)
    count = initial.size
    def pack(z):
        return np.concatenate((z.real.ravel(), z.imag.ravel()))
    def unpack(y):
        return (y[:count] + 1j*y[count:]).reshape(initial.shape)
    def field(t, y):
        return pack(rhs(g, unpack(y), viscosity))
    horizon = steps * dt
    ivp = solve_ivp(field, (0., horizon), pack(initial), method='DOP853',
                    rtol=rtol, atol=atol)
    if not ivp.success:
        raise RuntimeError(ivp.message)
    reference = enforce_reality(g, project_state(g, unpack(ivp.y[:, -1])))
    obs = lambda u: {
        'energy': total_energy(u),
        'weighted_five_halves': weighted_five_halves(g, u),
        'vorticity_fourier_l1': vorticity_fourier_l1(g, u)
    }
    a, b = obs(rk), obs(reference)
    output = {
        'schema': 'dashi.verid.ns_cross_integrator.v1',
        'seed': seed, 'cutoff': cutoff, 'steps': steps, 'dt': dt,
        'horizon': horizon, 'viscosity': viscosity,
        'numerical_model': 'explicit fixed-step RK4',
        'simulation_reference': 'adaptive SciPy DOP853',
        'shared_spatial_rhs': True,
        'independent_time_integrators': True,
        'rk4': a, 'dop853': b,
        'absolute_discrepancy': {k: abs(a[k]-b[k]) for k in a},
        'modal_l2_discrepancy': float(np.linalg.norm(rk-reference)),
        'reference_solver_nfev': ivp.nfev,
        'authority': {
            'finite_numerical_contact': True,
            'spatial_rhs_independent': False,
            'rigorous_a_posteriori_error_bound': False,
            'physical_measurement': False,
            'continuum_or_clay_result': False,
            'automatic_semantic_promotion': False
        },
        'next_experiment': 'vary cutoff or initial modes and measure residual-relevant observable disagreement',
    }
    output['digest'] = digest(output)
    return output

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--seed',type=int,default=101)
    p.add_argument('--cutoff',type=int,default=2)
    p.add_argument('--steps',type=int,default=8)
    p.add_argument('--dt',type=float,default=0.002)
    p.add_argument('--output-json',type=Path,required=True)
    args=p.parse_args()
    data=evaluate(args.seed,args.cutoff,args.dt,args.steps)
    args.output_json.parent.mkdir(parents=True,exist_ok=True)
    args.output_json.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    print(data['digest'])

if __name__=='__main__':
    main()
