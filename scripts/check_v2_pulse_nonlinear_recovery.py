#!/usr/bin/env python3
"""V2 illustrative, source-attributed *not hardware identified* pulse control audit.

This is the conventional pulse-efficiency steelman, inspired by (but not
identified with) independent Smith/Filsinger timed-pump work.  It supplies
both the nonlinear, independently modulated magnetic identity and a closed-
form falling-reluctance pulse-window current/copper/switching trade-off.

No measurements of @madscience369 V2 winding count, L(theta), pulse timing,
converter topology, current or loss coefficients are assumed or manufactured.
"""
from __future__ import annotations
import json
import math
from dataclasses import dataclass, asdict
import numpy as np
import sympy as s


def nonlinear_identity():
    """SymPy exact magnetic-coenergy, flux, torque and modulation work identity."""
    theta, current, u = s.symbols('theta current u', real=True)
    omega, di, du = s.symbols('omega di du', real=True)
    L0, A, B, k, beta0, beta1 = s.symbols('L0 A B k beta0 beta1', real=True)
    L = L0 + A * s.cos(k * theta) + B*u
    beta = beta0 + beta1 * u
    coenergy = s.Rational(1,2)*L*current**2 - s.Rational(1,4)*beta*current**4
    flux = s.diff(coenergy, current)
    torque = s.diff(coenergy, theta)
    modulation_force = s.diff(coenergy, u)
    energy = current * flux - coenergy
    def derivative(expr):
        return s.diff(expr, current)*di + s.diff(expr, theta)*omega + s.diff(expr, u)*du
    residual = s.trigsimp(s.simplify(s.expand(current*derivative(flux)
                           - derivative(energy) - torque*omega - modulation_force*du)))
    assert residual == 0
    # With u fixed, control doesn't inject power; no free gain is admitted.
    assert s.simplify(modulation_force.subs({B:0, beta1:0})) == 0
    # Linear recovery in the beta=0, B=0 corner preserves familiar formula.
    assert s.simplify(torque.subs({beta0:0,beta1:0,B:0})
                     - s.Rational(1,2)*current**2*s.diff(L0 + A*s.cos(k*theta),theta)) == 0
    return dict(identity='i*d(lambda)/dt = d(U)/dt + tau*omega + (dWco/du)*du/dt',
                residual='0', saturated_flux=str(flux), magnetic_energy=str(energy),
                torque=str(torque), modulation_coenergy_force=str(modulation_force),
                limitation='Reversible differentiable coenergy; no hysteresis or switch dynamics included')


@dataclass(frozen=True)
class Candidate:
    rotor_rpm: float = 2354.0  # reel-reported, *not* motor-map validation
    mean_mechanical_extraction_w: float = 45.0  # hypothetical objective, NOT measured shaft transfer
    l0_h: float = 0.040
    l_harmonic_h: float = 0.012
    pole_pairs: int = 4
    phase_r_ohm: float = 1.0
    current_limit_a: float = 8.0
    switch_fixed_j: float = 0.002
    switch_per_i2_j_per_a2: float = 0.00015
    other_loss_w: float = 0.5

    def validate(self):
        if self.pole_pairs<1 or self.rotor_rpm<=0 or self.mean_mechanical_extraction_w<=0:
            raise ValueError('positive shaft and rotor parameters required')
        if not (self.l0_h > abs(self.l_harmonic_h)>0):
            raise ValueError('L(theta) must be positive and nonconstant')
        if min(self.phase_r_ohm,self.current_limit_a,self.other_loss_w)<0:
            raise ValueError('negative resistance/current/other loss')
        if min(self.switch_fixed_j,self.switch_per_i2_j_per_a2)<0:
            raise ValueError('negative switch work')


def pulse_window(model: Candidate, q: float):
    """Exact angular mean for constant current during sin(k*theta)>q.

    Generator extraction uses falling L, i.e. positive sin(k*theta). At q=0
    current is supplied over all falling positions; q increases selectivity.
    Target magnetic mechanical extraction is fixed, not generator output.
    This is a static ideal pulse family: switching wavefronts/slew/voltage,
    diodes, C and nonlinear hysteresis are NOT certified here.
    """
    model.validate()
    if not (0<=q<1):raise ValueError('threshold 0<=q<1 required')
    omega=2*math.pi*model.rotor_rpm/60
    # For k repeated sine periods per revolution, pulse-work averages are
    # independent of k; k enters the mechanical torque coefficient and event count.
    active_fraction=math.acos(q)/math.pi
    active_sine_mean=math.sqrt(1-q*q)/math.pi
    torque_coefficient=.5*model.l_harmonic_h*model.pole_pairs*omega
    peak_i2=model.mean_mechanical_extraction_w/(torque_coefficient*active_sine_mean)
    current=math.sqrt(peak_i2)
    copper=model.phase_r_ohm*peak_i2*active_fraction
    # Exactly two transitions per pulse, pole_pairs pulses per revolution.
    transitions_per_second=2*model.pole_pairs*model.rotor_rpm/60
    switch_loss=transitions_per_second*(model.switch_fixed_j+model.switch_per_i2_j_per_a2*peak_i2)
    useful=model.mean_mechanical_extraction_w-copper-switch_loss-model.other_loss_w
    return dict(q=q,active_fraction=active_fraction,peak_current_a=current,
                current_limit_feasible=current<=model.current_limit_a,
                mechanical_extraction_w=model.mean_mechanical_extraction_w,
                copper_loss_w=copper,switch_loss_w=switch_loss,
                other_loss_w=model.other_loss_w,
                ideal_net_bus_w=useful,
                complete_balance_residual_w=model.mean_mechanical_extraction_w-(useful+copper+switch_loss+model.other_loss_w),
                note='Conditional model with fixed mechanical extraction and no reactive-power processing losses')


def optimize_grid(model: Candidate, q_grid: np.ndarray | None=None):
    grid=np.linspace(0,.98,981) if q_grid is None else q_grid
    cases=[pulse_window(model,float(q)) for q in grid]
    feasible=[v for v in cases if v['current_limit_feasible']]
    if not feasible:raise ValueError('no current-feasible pulse windows')
    best=max(feasible,key=lambda x:x['ideal_net_bus_w'])
    baseline=pulse_window(model,0.)
    return dict(model=asdict(model),baseline=baseline,best=best,
                feasible_count=len(feasible),tested_count=len(cases),
                improvement_w=best['ideal_net_bus_w']-baseline['ideal_net_bus_w'])


def phase_symmetry_null():
    """Closed analytic N-phase identity for matched independent current waves."""
    t=s.symbols('t', real=True)
    # sinusoidal current squared allocations have mean n*i^2/2; fixed total
    # current squared budget Q makes copper independent of n. Illustrates why
    # phase counts affect ripple, switching and voltage, not intrinsically gain.
    n,Q,R=s.symbols('n Q R', positive=True)
    per_phase_mean_i2=Q/n
    total_copper=s.simplify(n*R*per_phase_mean_i2)
    assert s.simplify(total_copper-R*Q)==0
    return dict(matched_copper='R*Q independent of n', caveat='identical winding R and aggregate mean i^2 budget')


def run():
    model=Candidate()
    nonlinear=nonlinear_identity()
    results=optimize_grid(model)
    cases=[pulse_window(model,q) for q in (0,.25,.5,.7,.8,.9)]
    assert all(abs(c['complete_balance_residual_w'])<1e-9 for c in cases)
    assert results['best']['ideal_net_bus_w']>=results['baseline']['ideal_net_bus_w']
    return dict(scope='Hypothetical conventional generator; NOT V2 calibration',
                original_attribution='@madscience369 V2 reel: only RPM and claimed electrical figures; no topology identified',
                donor_attribution='Smith/Filsinger timed-pump Hamiltonian: distinct source; DASHI cross-domain analogy only',
                nonlinear_identity=nonlinear,phase_null=phase_symmetry_null(),
                pulse_model=results,examples=cases,
                physics_gates=['source-selected winding/switch network','measured nonlinear lambda(theta,i,T) or coenergy map',
                               'proper signed modulation actuator work','actual pulse slew and converter source/load ports',
                               'timing/rotor phase and all-power calibration','continuous voltage and thermal bounds',
                               'hysteresis, saturation, eddy/core and mutual flux loss models'])

if __name__=='__main__':
    print(json.dumps(run(),indent=2))