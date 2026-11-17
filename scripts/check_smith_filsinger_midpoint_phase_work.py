#!/usr/bin/env python3
"""Conditional two-mode TWO-PORT source work; no Filsinger measurements.

Reuse canonical reflection, phase, finite flight, source and PR #1521
environment-access owners. Natural incident wave is independently stipulated:
its frequency/coherence/power are not derived from a fair-weather DC current.

TCMT: da/dt = (i Omega - Gamma_i - Gamma_L - K K^T/2)a + K s_in;
      s_out = -s_in + K^T a. Port power = |s|^2.
At harmonic exp(i omega t):
      [Gamma_i + Gamma_L + K K^T/2 + i(omega I-Omega)]a=K s_in.
The shared K K^T/2 term enforces radiative source backaction and passivity.
A pure-delay phase at the observation region is only a phasor diagnostic, not
a full retarded Maxwell/plasma Green's function or actual device signal.
"""
from dataclasses import dataclass, replace
import cmath
import json
import math
import numpy as np

@dataclass(frozen=True)
class Params:
    ge_nat: float = .035
    ge_ctrl: float = .04
    gamma_internal: float = .02
    gamma_load: float = .05
    frequency: float = 1.
    detuning: float = .075
    conservative_coupling: float = .018
    natural_amp: float = .35
    controller_amp: float = .6
    natural_phase: float = 0.
    controller_phase: float = 0.
    branch_delays: tuple = (0.,0.)

def matrices(p):
    for v in (p.ge_nat,p.ge_ctrl,p.gamma_internal,p.gamma_load):
        if not math.isfinite(v) or v<0:raise ValueError('nonnegative port rates required')
    for v in (p.frequency,p.detuning,p.conservative_coupling,p.natural_amp,
              p.controller_amp,p.natural_phase,p.controller_phase,*p.branch_delays):
        if not math.isfinite(v):raise ValueError('finite parameters required')
    if any(t<0 for t in p.branch_delays):raise ValueError('causal observation delays required')
    k=np.array([[math.sqrt(p.ge_nat),math.sqrt(p.ge_ctrl)],
                [math.sqrt(p.ge_nat),-math.sqrt(p.ge_ctrl)]],dtype=float)
    om=np.array([[p.frequency+p.detuning,p.conservative_coupling],
                 [p.conservative_coupling,p.frequency-p.detuning]])
    gamma=(p.gamma_internal+p.gamma_load)*np.eye(2)+.5*k@k.T
    return k,om,gamma,gamma+1j*(p.frequency*np.eye(2)-om)

def solve(p):
    k,om,gamma,m=matrices(p)
    incoming=np.array([p.natural_amp*cmath.exp(1j*p.natural_phase),
                       p.controller_amp*cmath.exp(1j*p.controller_phase)])
    state=np.linalg.solve(m,k@incoming)
    outgoing=-incoming+k.T@state
    pin=np.abs(incoming)**2
    pout=np.abs(outgoing)**2
    signed=pin-pout
    useful=2*p.gamma_load*np.vdot(state,state).real
    heat=2*p.gamma_internal*np.vdot(state,state).real
    observed=state*np.exp(-1j*p.frequency*np.array(p.branch_delays))
    denom=sum(np.abs(observed)**2)
    return dict(natural_in=float(pin[0]),natural_out=float(pout[0]),
                controller_in=float(pin[1]),controller_out=float(pout[1]),
                natural_net=float(signed[0]),controller_net=float(signed[1]),
                load=float(useful),heat=float(heat),
                balance_residual=float(sum(signed)-useful-heat),
                relative_phase_rad=float(np.angle(observed[1]*np.conjugate(observed[0]))),
                circularity=float(2*np.imag(np.conjugate(observed[0])*observed[1])/denom if denom else 0.),
                modes=tuple(complex(v) for v in state))

def wrap_phase(x):return float(np.angle(np.exp(1j*x)))

def coherent_phase_scan(p=Params(),n=72):
    rows=[]
    for ph in np.linspace(0,2*np.pi,n,endpoint=False):
        r=solve(replace(p,controller_phase=float(ph)))
        rows.append(dict(controller_phase=float(ph),
            phase_at_receiver=r['relative_phase_rad'],
            natural_net=r['natural_net'],controller_net=r['controller_net'],
            useful_load=r['load'],internal_loss=r['heat'],
            balance_residual=r['balance_residual']))
    return rows

def incoherent_phase_average(p=Params(),n=256):
    # Independent uniform source phase, NOT an ambient field measurement.
    rows=[]
    for cp in (0.,math.pi/2,math.pi,3*math.pi/2):
        avg=np.zeros(4)
        for j in range(n):
            r=solve(replace(p,controller_phase=cp,natural_phase=2*math.pi*j/n))
            avg+=np.array([r['natural_net'],r['controller_net'],r['load'],r['heat']])/n
        rows.append(dict(controller_phase=cp,natural_net=avg[0],
              controller_net=avg[1],load=avg[2],heat=avg[3]))
    return rows

def phase_load_search(p=Params()):
    rows=[]
    for load in (.01,.025,.05,.075,.1,.16):
      for detune in (0.,.025,.05,.075,.1,.16):
       for ph in np.linspace(0,2*np.pi,48,endpoint=False):
        q=replace(p,gamma_load=load,detuning=detune,controller_phase=float(ph))
        r=solve(q)
        off=solve(replace(q,natural_amp=0.))
        rows.append(dict(load_coupling=load,detuning=detune,
            controller_phase=float(ph),load_power=r['load'],
            natural_net=r['natural_net'],controller_net=r['controller_net'],
            phase_at_receiver=r['relative_phase_rad'],circularity=r['circularity'],
            delta_load_on_off=r['load']-off['load'],
            no_natural_port_net=off['natural_net'],
            balanced=abs(r['balance_residual'])<1e-12))
    return dict(cases=len(rows),
        max_load=max(rows,key=lambda r:r['load_power']),
        max_positive_env_net=max(rows,key=lambda r:r['natural_net']),
        max_load_given_positive_env=max((r for r in rows if r['natural_net']>0),
                                        key=lambda r:r['load_power']),
        max_circularity=max(rows,key=lambda r:abs(r['circularity'])))

def exact_control_checks():
    p=Params()
    baseline=solve(p)
    no_nat=solve(replace(p,natural_amp=0.))
    no_ctrl=solve(replace(p,controller_amp=0.))
    blank=solve(replace(p,natural_amp=0.,controller_amp=0.))
    assert no_nat['natural_net']<=1e-12
    assert abs(blank['load'])<1e-12
    a=solve(replace(p,natural_amp=0.,controller_amp=.3))
    b=solve(replace(p,natural_amp=0.,controller_amp=.9))
    assert abs(wrap_phase(a['relative_phase_rad']-b['relative_phase_rad']))<1e-12
    assert max(abs(r['balance_residual']) for r in (baseline,no_nat,no_ctrl,blank))<1e-12
    return baseline,no_nat,no_ctrl

def run():
    p=Params()
    baseline,no_nat,no_ctrl=exact_control_checks()
    rows=coherent_phase_scan(p)
    return dict(scope='specified passive reciprocal two-port model; NOT original source measurements',
      existing_producers=['SmithFilsingerSunEarthCoupledSourceExact',
       'SmithFilsingerTimeIndexedTransferExact',
       'SmithFilsingerReflectedPortBidiExact',
       'smith_filsinger_reflection_energy_cut.py',
       'smith_filsinger_single_wave_fibonacci_modes.py',
       'PR #1521 passive Earth/air/soil admittance'],
      baseline={k:v for k,v in baseline.items() if k!='modes'},
      no_environment_incoming={k:v for k,v in no_nat.items() if k!='modes'},
      no_controller_incoming={k:v for k,v in no_ctrl.items() if k!='modes'},
      coherent_natural_net_range=[min(r['natural_net'] for r in rows),max(r['natural_net'] for r in rows)],
      coherent_load_range=[min(r['useful_load'] for r in rows),max(r['useful_load'] for r in rows)],
      phase_coherent_grid=rows,independently_random_environment=incoherent_phase_average(p),
      optimization=phase_load_search(p),
      original_world_gates=['S5c','S5d','S5e','S5f','S5g','S8c','S8d','P2','R2','R3','D1','D2'])

if __name__=='__main__':print(json.dumps(run(),indent=2))
