#!/usr/bin/env python3
"""Constructive periodic reluctance generator with feasible averaged bus voltage.

For each of m shifted coils, exact prescribed periodic current i_j(θ) is a
solution of v_j = R i_j + d/dt(L_j i_j), not a desired rectangular current
silently assumed feasible. It has exact cycle storage closure, finite voltage,
positive mechanical generation and explicit copper loss. Identical rotated
coil maps, no saturation/core losses, ideal averaged voltage (NOT transistor
PWM, original V2, or instantaneous coupling beyond quasistatic regime).

Homogeneous Poincare multiplier for psi=L*i is exp(-R*T/sqrt(L0²-A²)),
so for R>0, L0>A and periodic forcing there is a unique attractive periodic
solution. This is restricted scalar positive-R model only.
"""
from __future__ import annotations
from dataclasses import dataclass, asdict
import json
import math
import numpy as np
import sympy as sp


@dataclass(frozen=True)
class PeriodicModel:
    rpm:float=2354.0
    harmonic:int=4
    l0_h:float=.040
    harmonic_h:float=.012
    resistance_ohm:float=1.
    i0_a:float=1.
    i1_a:float=.6
    bus_voltage_v:float=320.

    def validate(self):
        if not (self.rpm>0 and self.harmonic>=1 and self.l0_h>abs(self.harmonic_h)>0
                and self.resistance_ohm>0 and self.bus_voltage_v>0
                and self.i0_a>=abs(self.i1_a)>0):
            raise ValueError('positive L, R, speed, and nonnegative current assumed')

    @property
    def omega(self):return 2*math.pi*self.rpm/60
    @property
    def period_s(self):return 2*math.pi/self.omega
    @property
    def contraction(self):
        self.validate()
        return math.exp(-self.resistance_ohm*self.period_s/
                        math.sqrt(self.l0_h**2-self.harmonic_h**2))


def phase_exact_identity():
    """Derive individual coil v*i = R*i^2 + dU/dt + tau*omega."""
    x,I0,I1,L0,A,R,w,h,m=sp.symbols('x I0 I1 L0 A R w h m',real=True)
    i=(I0+I1*sp.sin(x))/sp.sqrt(m)
    L=L0+A*sp.cos(x)
    di=sp.diff(i,x)*h*w
    dL=sp.diff(L,x)*h*w
    v=R*i+L*di+dL*i
    U=sp.Rational(1,2)*L*i*i
    dU=sp.diff(U,x)*h*w
    tau=sp.Rational(1,2)*i*i*sp.diff(L,x)*h
    assert sp.simplify(sp.expand(v*i-R*i*i-dU-tau*w))==0
    return {'exact_linear_coenergy_identity':'0',
            'periodic_i':'(I0+I1*sin(h*theta-phi))/sqrt(m)',
            'periodic_L':'L0+A*cos(h*theta-phi)',
            'voltage':'R*i + L*di/dt + (dL/dt)*i'}


def certificate(model:PeriodicModel,m:int,samples:int=1024):
    model.validate()
    if m<3 or samples<4*m:raise ValueError('three or more phases and adequate sample points')
    x=np.linspace(0,2*math.pi,samples,endpoint=False)
    shift=2*math.pi*np.arange(m)/m
    xx=x[:,None]-shift[None,:]
    sqrtm=math.sqrt(m)
    i=(model.i0_a+model.i1_a*np.sin(xx))/sqrtm
    di=model.i1_a*np.cos(xx)*model.harmonic*model.omega/sqrtm
    L=model.l0_h+model.harmonic_h*np.cos(xx)
    dL=-model.harmonic_h*model.harmonic*model.omega*np.sin(xx)
    v=model.resistance_ohm*i+L*di+dL*i
    tau=(-.5*model.harmonic_h*model.harmonic*np.sin(xx)*i*i).sum(axis=1)
    energy=.5*np.sum(L*i*i,axis=1)
    port=(v*i).sum(axis=1)
    cu=model.resistance_ohm*(i*i).sum(axis=1)
    # Time derivative evaluated analytically (not inferred from total port).
    dU=(.5*dL*i*i+L*i*di).sum(axis=1)
    residual=port-cu-dU-tau*model.omega
    min_i=float(i.min());peak_v=float(np.abs(v).max())
    bound_v=(model.resistance_ohm*(model.i0_a+model.i1_a)
             +(model.l0_h+model.harmonic_h)*model.harmonic*model.omega*model.i1_a
             +model.harmonic_h*model.harmonic*model.omega*(model.i0_a+model.i1_a))/sqrtm
    mean_extraction=.5*model.harmonic_h*model.harmonic*model.omega*model.i0_a*model.i1_a
    mean_cu=model.resistance_ohm*(model.i0_a**2+.5*model.i1_a**2)
    bus_ideal=mean_extraction-mean_cu
    predicted_ripple=(model.i1_a/(4*math.sqrt(2)*model.i0_a)) if m==3 else 0.
    observed_ripple=float(np.std(tau)/abs(np.mean(tau)))
    tol=1e-9*max(1.,mean_extraction)
    assert max(abs(residual))<tol
    assert abs(float(port.mean())+bus_ideal)<tol
    assert abs(float(cu.mean())-mean_cu)<tol
    assert abs(float(tau.mean())*model.omega+mean_extraction)<tol
    assert abs(observed_ripple-predicted_ripple)<1e-10
    assert bound_v>=peak_v
    return {
        'phases':m,'mean_shaft_extraction_w':mean_extraction,
        'mean_copper_w':mean_cu,'ideal_net_export_w':bus_ideal,
        'peak_applied_voltage_v':peak_v,'analytic_voltage_upper_v':bound_v,
        'bus_voltage_feasible_certified':bool(bound_v<=model.bus_voltage_v),
        'minimum_winding_current_a':min_i,
        'current_nonnegative_certified':bool(model.i0_a>=abs(model.i1_a)),
        'fractional_torque_ripple_rms':observed_ripple,
        'predicted_exact_ripple_rms':predicted_ripple,
        'cycle_flux_energy_endpoint_equal':'follows exactly from 2pi-periodic current and L',
        'periodic_orbit_unique_attractive':True,'poincare_contraction':model.contraction,
        'max_pointwise_residual_w':float(max(abs(residual))),
        'energy_storage_cycle_mean_derivative_w':float(dU.mean()),
        'conditional_scope':'linear decoupled phase winding + ideal continuous averaged PWM; finite voltage proven by conservative analytic envelope; no physical parameters calibrated'
    }


def max_generation_with_fixed_rms(model:PeriodicModel):
    """Analytic optimum in the nonnegative sine-current family.

    With S=I0²+I1²/2 fixed, and 0<=I1<=I0, maximum of I0*I1
    occurs exactly at I0=I1=sqrt(2S/3). Proof: put b=I1²/S;
    product²/S² = b(1-b/2); b in [0,2/3], derivative 1-b>0.
    Any voltage cap may cut the feasible set further, so this is a
    lossless-geometry conditional upper bound, not general converter optimum.
    """
    model.validate()
    S=model.i0_a**2+.5*model.i1_a**2
    Iopt=math.sqrt(2*S/3)
    torque_opt=.5*model.harmonic_h*model.harmonic*model.omega*Iopt*Iopt
    return {'fixed_aggregate_mean_current_squared_a2':S,
            'optimal_unipolar_i0_a':Iopt,'optimal_unipolar_i1_a':Iopt,
            'max_mean_mechanical_extraction_w':torque_opt,
            'model_assumption':'identical independent sinusoidal coils, voltage unconstrained within family',
            'proof':'for b=I1²/S<=2/3, product²/S²=b*(1-b/2), derivative 1-b>0'}



def causal_sensor_delay_weld(model:PeriodicModel, flight_s:float,
                             angular_accel_bound_rad_s2:float=0.):
    """A *delayed* rotor observation may be extrapolated using known speed.

    Under constant omega, an uncompensated coil-current phase lag δ=h*omega*tau
    multiplies average generation by cos δ. Predicting current theta from an
    older measurement is feed-forward inference, NOT propagation of new state
    faster than light. If |theta_ddot|<=a and the predictor uses old omega,
    |phase prediction error|<=.5*h*a*tau², by Taylor remainder.
    """
    model.validate()
    if flight_s<0 or angular_accel_bound_rad_s2<0:
        raise ValueError('flight/acceleration nonnegative')
    delta=model.harmonic*model.omega*flight_s
    shaft=.5*model.harmonic_h*model.harmonic*model.omega*model.i0_a*model.i1_a
    return {'delay_s':flight_s,'uncompensated_electrical_phase_rad':delta,
            'uncompensated_generation_w':shaft*math.cos(delta),
            'uncompensated_loss_from_lag_w':shaft*(1-math.cos(delta)),
            'predicted_phase_error_bound_rad':.5*model.harmonic*angular_accel_bound_rad_s2*flight_s**2,
            'source_model':'delayed observation plus locally predictive feed-forward; not instant remote information',
            'limitations':'constant speed for exact cos loss, no PWM edge/feedback instability guarantee'}

def run():
    model=PeriodicModel()
    rows=[certificate(model,m) for m in range(3,13)]
    assert all(r['bus_voltage_feasible_certified'] for r in rows)
    assert all(abs(r['energy_storage_cycle_mean_derivative_w'])<1e-10 for r in rows)
    return {'scope':'constructed stable periodic averaged-current motor certificate, not original V2',
            'model':asdict(model),'exact_identity':phase_exact_identity(),
            'restricted_global_current_allocation':max_generation_with_fixed_rms(model),
            'delayed_rotor_sensor_example':causal_sensor_delay_weld(model,.5/(.7*299_792_458.0)),
            'phase_rows':rows,'gates_open':['actual transistor PWM ripple/transition envelope',
                                         'saturating coupled nonlinear periodic orbit',
                                         'retarded field-to-motor controller weld',
                                         'original V2 physical geometry and full energy boundary']}

if __name__=='__main__':print(json.dumps(run(),indent=2))