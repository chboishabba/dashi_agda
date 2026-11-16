#!/usr/bin/env python3
"""Complementary branch timing against a FIXED naturally biased DC source.

This differs physically from phase-locking independent incident RF waves.
A common controller can phase two internal branches relative to each other
without any coherent external waveform. A nonnegative controller auxiliary
cost is explicit. Voc, Rs, Gs are assumed normalized model parameters,
NOT an actual Filsinger Earth electrode source or weather mechanism.
"""
from dataclasses import dataclass, replace
import json, math
import numpy as np
import sympy as sp

@dataclass(frozen=True)
class DCParams:
    voc: float = 1.
    rs: float = 1.
    mean_branch_G: float = .5
    amplitude_branch_G: float = .35
    controller_cost: float = .01
    samples: int = 2048

def exact_thevenin_square():
    g=sp.symbols('G',positive=True)
    # Fixed Voc=1, Rs=1: ceiling minus power is a nonnegative square.
    assert sp.simplify(sp.Rational(1,4)-g/(1+g)**2-
                       (g-1)**2/(4*(1+g)**2))==0
    t=sp.symbols('theta',real=True)
    assert sp.trigsimp(sp.sin(t)+sp.sin(t+sp.pi))==0
    return True

def cycle(phase,p=DCParams()):
    vals=(phase,p.voc,p.rs,p.mean_branch_G,p.amplitude_branch_G,p.controller_cost)
    if not all(math.isfinite(v) for v in vals):
        raise ValueError('finite model parameters required')
    if p.voc<0 or p.rs<=0 or p.mean_branch_G<p.amplitude_branch_G or p.amplitude_branch_G<0 or p.controller_cost<0:
        raise ValueError('nonnegative branch/source/actuation parameters required')
    if p.samples<16:raise ValueError('sample count too small')
    t=np.arange(p.samples)*2*np.pi/p.samples
    g1=p.mean_branch_G+p.amplitude_branch_G*np.sin(t)
    g2=p.mean_branch_G+p.amplitude_branch_G*np.sin(t+phase)
    conductance=g1+g2
    current=p.voc*conductance/(1+p.rs*conductance)
    terminal=p.voc-p.rs*current
    natural=p.voc*current
    load=terminal**2*conductance
    feedloss=p.rs*current**2
    controller=np.full(p.samples,p.controller_cost)
    residual=np.max(np.abs(natural+controller-load-feedloss-controller))
    return dict(phase_rad=float(phase),natural_supplied=float(np.mean(natural)),
        load_work=float(np.mean(load)),feed_loss=float(np.mean(feedloss)),
        controller_input=float(np.mean(controller)),
        controller_aux_loss=float(np.mean(controller)),
        net_useful_after_controller_cost=float(np.mean(load-controller)),
        ripple_G=float(np.ptp(conductance)),peak_load=float(np.max(load)),
        energy_residual=float(residual))

def run():
    exact_thevenin_square()
    p=DCParams()
    grid=np.linspace(0,2*np.pi,129)
    rows=[cycle(float(x),p) for x in grid]
    opposed=cycle(math.pi,p)
    inphase=cycle(0.,p)
    mismatch=[cycle(float(x),replace(p,rs=3.)) for x in grid]
    best=max(rows,key=lambda r:r['load_work'])
    assert abs(best['phase_rad']-math.pi)<1e-9
    assert opposed['ripple_G']<1e-12
    assert opposed['load_work']>inphase['load_work']
    return dict(scope='conditional biased DC Thevenin source, not measured Earth-terminal work',
      exact_matching_slack='Pmax-P(G)=Voc^2*(Rs*G-1)^2/[4*Rs*(1+Rs*G)^2]',
      port_conservation='Pnatural+Pcontroller=Pload+Pfeed_loss+Pcontroller_aux_loss',
      same_source_anti_phase=opposed,same_source_in_phase=inphase,
      best_in_fixed_rs_one=best,
      source_resistance_mismatch_best=max(mismatch,key=lambda r:r['load_work']),
      phase_grid=rows)

if __name__=='__main__':print(json.dumps(run(),indent=2))
