#!/usr/bin/env python3
"""Finite-memory, variable-load source: exact segment-integrated source work.

NON-ORIGINAL conditional linear source, not an Earth/atmosphere instrument model.

    C dv/dt = g(V_up-v) - G(t)v,     G(t) = G_1(t)+G_2(t) >= 0.

Natural upstream source work = integral V_up*g*(V_up-v) dt
Natural terminal work        = integral v*g*(V_up-v) dt
Feeder loss                 = integral g*(V_up-v)^2 dt
Load work                   = integral G(t)*v^2 dt
Store U                     = C*v^2/2

W_upstream = W_feed + W_load + DeltaU.
W_terminal = W_load + DeltaU.
W_terminal <= g*V_up^2*T/4, since
  g*V_up^2/4 - g*v*(V_up-v) = g*(v-V_up/2)^2 >= 0.

Piecewise-constant G_j throughout each interval; the ODE and work integrals
are EXACT for each interval (no Euler integration); sine branch waveform is
sampled at interval MIDPOINTS, not an exact continuous-sine solution.
A regulator's controller energy is counted as distinct auxiliary input+loss;
no zero-power modulator is inferred for actual switching electronics.

The external voltage source is stipulated. A fixed V_up is not a measured
natural source; only a measured source feed, admittance and return can
promote this illustrative model to a physical device.
"""
from dataclasses import dataclass, replace
import json
import math
from typing import NamedTuple


@dataclass(frozen=True)
class Source:
    upstream_v: float = 1.0
    feed_g: float = 1.0
    capacitance: float = 1.0
    controller_cost_rate: float = 0.01


@dataclass(frozen=True)
class Branches:
    mean_g: float = 0.5
    amp_g: float = 0.35
    phase: float = math.pi
    period: float = 2 * math.pi
    intervals: int = 256


class Step(NamedTuple):
    v1: float
    upstream: float
    terminal: float
    feeder_heat: float
    load: float
    delta_store: float
    match_deficit: float
    controller: float
    residual: float


def validate(src: Source, b: Branches):
    if not all(math.isfinite(x) for x in (src.upstream_v, src.feed_g,
                  src.capacitance, src.controller_cost_rate, b.mean_g,
                  b.amp_g, b.phase, b.period)):
        raise ValueError('All parameters must be finite')
    if src.feed_g < 0 or src.capacitance <= 0 or src.controller_cost_rate < 0:
        raise ValueError('Invalid source conductance/capacitance/cost')
    if b.amp_g < 0 or b.mean_g < b.amp_g or b.period <= 0 or b.intervals < 8:
        raise ValueError('Negative conductance, invalid time or too few intervals')


def exact_segment(src: Source, v0: float, load_g: float, dt: float) -> Step:
    """Exact work integrals for constant g, G, Vup, C over dt."""
    if not all(math.isfinite(x) for x in (v0, load_g, dt)) or load_g < 0 or dt < 0:
        raise ValueError('Invalid state, load or duration')
    g, V, C = src.feed_g, src.upstream_v, src.capacitance
    lam = (g + load_g) / C
    if lam == 0:
        v1 = v0
        int_v = v0 * dt
        int_v2 = v0 * v0 * dt
    else:
        v_inf = g * V / (g + load_g)
        d = v0 - v_inf
        ex = math.exp(-lam * dt)
        i_exp = -math.expm1(-lam * dt) / lam
        i_exp2 = -math.expm1(-2 * lam * dt) / (2 * lam)
        v1 = v_inf + d * ex
        int_v = v_inf * dt + d * i_exp
        int_v2 = v_inf * v_inf * dt + 2 * v_inf * d * i_exp + d * d * i_exp2
    w_up = g * (V * V * dt - V * int_v)
    w_feed = g * (V * V * dt - 2 * V * int_v + int_v2)
    w_term = g * (V * int_v - int_v2)
    w_load = load_g * int_v2
    du = C * (v1 * v1 - v0 * v0) / 2
    match_deficit = g * (int_v2 - V * int_v + V * V * dt / 4)
    aux = src.controller_cost_rate * dt
    residual = w_up + aux - w_feed - w_load - du - aux
    return Step(v1,w_up,w_term,w_feed,w_load,du,match_deficit,aux,residual)


def branch_g(b: Branches, idx: int) -> tuple[float,float]:
    theta = 2 * math.pi * (idx + .5) / b.intervals
    return b.mean_g + b.amp_g * math.sin(theta), b.mean_g + b.amp_g * math.sin(theta+b.phase)


def one_cycle(src: Source = Source(), b: Branches = Branches(), v0: float = 0.5):
    validate(src, b)
    dt = b.period / b.intervals
    v = v0
    sums = {key:0. for key in ('upstream','terminal','feeder_heat','load',
              'delta_store','match_deficit','controller','residual')}
    for i in range(b.intervals):
        a, c = branch_g(b,i)
        q = exact_segment(src,v,a+c,dt)
        v = q.v1
        for key in sums:
            sums[key] += getattr(q,key)
    cap = src.feed_g*src.upstream_v**2*b.period/4
    return dict(v_start=v0,v_final=v,storage_initial=src.capacitance*v0*v0/2,
       storage_final=src.capacitance*v*v/2,source_cap=cap,
       **sums,
       terminal_cap_residual=sums['terminal']+sums['match_deficit']-cap,
       whole_cycle_residual=sums['upstream']-sums['feeder_heat']-sums['load']-sums['delta_store'],
       net_load_after_controller=sums['load']-sums['controller'],
       output_excess_over_static_cap=sums['load']-cap)


def periodic_state(src: Source = Source(), b: Branches = Branches()):
    """Stable periodic fixed point of exact (piecewise-constant) affine cycle."""
    validate(src,b)
    if src.feed_g == 0 and b.mean_g == 0:
        return 0.0
    q0=one_cycle(src,b,0.0)['v_final']
    q1=one_cycle(src,b,1.0)['v_final']
    a=q1-q0
    if not (0 <= a < 1):
        raise ValueError('No unique attracting period in selected case')
    return q0/(1-a)


def compare(src: Source = Source(), b: Branches = Branches()):
    results=[]
    for phase in (0, math.pi/4, math.pi/2, 3*math.pi/4, math.pi):
        q=replace(b,phase=phase)
        r=one_cycle(src,q,periodic_state(src,q))
        results.append(dict(phase_deg=round(phase*180/math.pi,2),
            load=r['load'],natural_terminal=r['terminal'],upstream=r['upstream'],
            store_delta=r['delta_store'],source_cap=r['source_cap'],
            match_deficit=r['match_deficit'],controller=r['controller'],
            net_after_controller=r['net_load_after_controller']))
    return results


def fairweather_column(area_m2=1.,voc=250000.,j=2.36e-12, tau_seconds=600.):
    """HYPOTHETICAL fixed-source full-column equivalents, not local plate.

    Illustrative source capacitance C=g*tau is *assumed*; observed global GEC
    7-12min relaxation must NOT be imported as local collector capacitance.
    """
    if min(area_m2,voc,j,tau_seconds)<=0:raise ValueError('positive physical inputs')
    g=j*area_m2/voc
    c=g*tau_seconds
    return dict(area_m2=area_m2,short_circuit_current_A=j*area_m2,
        fixed_source_voc_V=voc,source_conductance_S=g,
        matched_power_W=g*voc*voc/4,
        matched_energy_60s_J=g*voc*voc*60/4,
        illustrative_C_F=c,
        illustrative_stored_energy_at_half_Voc_J=c*(voc/2)**2/2,
        hypothetical_tau_seconds=tau_seconds,
        source_identity='ideal fixed full-column Thevenin only; NOT Filsinger terminal')


def summary():
    src=Source()
    b=Branches()
    cyc=compare(src,b)
    transient=one_cycle(src,b,v0=src.upstream_v*2)
    donor=Source(upstream_v=1.,feed_g=0.,capacitance=1.,controller_cost_rate=.01)
    donor_cycle=one_cycle(donor,replace(b,phase=math.pi,period=20.),v0=1.)
    zero=one_cycle(replace(donor,upstream_v=0.),b,v0=0.)
    return dict(scope='conditional source with exact segment work, not measured Earth or Filsinger',
      equations=['C dv/dt=g(Vup-v)-G(t)v',
        'Wup=Wfeedloss+Wload+DeltaU',
        'Wterm=Wload+DeltaU',
        'Wterm+g*integral(v-Vup/2)^2 dt=g*Vup^2*T/4'],
      periodic_5phases=cyc,initial_overcharge_transient=transient,
      unpowered_finite_donor=donor_cycle,empty_control=zero,
      fairweather_ideal_full_column=fairweather_column(),
      original_physical_gates_open=['S0','P1','P2','R1','R2','R3','D1','D2'])

if __name__=='__main__':
    print(json.dumps(summary(),indent=2))
