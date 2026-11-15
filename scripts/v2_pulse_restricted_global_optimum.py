#!/usr/bin/env python3
"""Global optimum in ONE specifically stated ideal reluctance pulse-window class.

This closes the scalar-in-q analytic minimization, not the full nonlinear
multi-winding finite-bus optimal control or the original @madscience369 V2.
At fixed Pshaft: copper Kc acos(q)/sqrt(1-q²), per-edge I² switching
Ksw/sqrt(1-q²), fixed switch energy independent of q. For Kc>0,
N(q)=Kc*(q acos(q)-sqrt(1-q²))+Ksw*q, and
N'(q)=Kc acos(q)+Ksw>0 on (0,1). Thus dLoss/dq crosses zero
at most once and the constrained minimizer is min(q*,q_current_max).
Proof of the derivative is checked symbolically in SymPy; monotonicity uses
acos(q)>0, Kc>0, Ksw>=0.  Floating bisection is not Agda kernel proof.
"""
import json
import math
from dataclasses import asdict
from pathlib import Path
import sys

import sympy as sy
from scipy.optimize import brentq

sys.path.insert(0,str(Path(__file__).resolve().parent))
from check_v2_pulse_nonlinear_recovery import Candidate, pulse_window, optimize_grid


def derivative_identity():
    q,Kc,Ksw=sy.symbols('q Kc Ksw',positive=True,real=True)
    f=(Kc*sy.acos(q)+Ksw)/sy.sqrt(1-q**2)
    numerator=Kc*(q*sy.acos(q)-sy.sqrt(1-q**2))+Ksw*q
    assert sy.simplify(sy.diff(f,q)-numerator/(1-q**2)**sy.Rational(3,2))==0
    assert sy.simplify(sy.diff(numerator,q)-(Kc*sy.acos(q)+Ksw))==0
    assert sy.simplify(f.subs(q,0)-(sy.pi*Kc/2+Ksw))==0
    return {'first_derivative_exact':True,'unique_zero_derivative_exact':True,
            'monotonicity':'Nprime=Kc*acos(q)+Ksw>0 for 0<=q<1 and Kc>0, Ksw>=0'}


def restricted_global_optimum(p:Candidate=Candidate()):
    p.validate()
    omega=2*math.pi*p.rotor_rpm/60
    base=p.l_harmonic_h*p.pole_pairs*omega
    if base<=0:raise ValueError('nonpositive inductance harmonic work')
    current_squared_const=2*math.pi*p.mean_mechanical_extraction_w/base
    if current_squared_const>p.current_limit_a**2:
        raise ValueError('no constant-current pulse window satisfies current limit')
    qmax=math.sqrt(max(0.,1-(current_squared_const/p.current_limit_a**2)**2))
    KC=2*p.phase_r_ohm*p.mean_mechanical_extraction_w/base
    switches_per_second=2*p.pole_pairs*p.rotor_rpm/60
    KS=switches_per_second*p.switch_per_i2_j_per_a2*current_squared_const
    def numerator(q):
        return KC*(q*math.acos(q)-math.sqrt(max(0,1-q*q)))+KS*q
    # If Ksw=0, the loss decreases all the way to qmax.
    root=brentq(numerator,0.,1.,xtol=1e-14) if KS>0 else 1.
    qstar=math.nextafter(qmax,0.) if qmax<=root and qmax>0 else min(qmax,root)
    optimum=pulse_window(p,qstar)
    if not optimum['current_limit_feasible']:
        raise AssertionError('current-limited optimum must be feasible')
    if abs(optimum['complete_balance_residual_w'])>1e-9:
        raise AssertionError('energy identity must close')
    grid=optimize_grid(p)
    assert optimum['ideal_net_bus_w']>=grid['best']['ideal_net_bus_w']-1e-7
    return {'scope':'GLOBAL only within q∈[0,1), ideal constant-current window family at FIXED mechanical extraction',
            'model':asdict(p),'q_max_from_current':qmax,'unconstrained_unique_minimum':root,
            'selected_q_global':qstar,'optimum':optimum,
            'grid_gap_w':optimum['ideal_net_bus_w']-grid['best']['ideal_net_bus_w'],
            'strict_proof':'dLoss/dq has strictly increasing numerator N; root unique; current feasible interval [0,qmax]',
            'not_proved':'finite slew, voltage, hysteresis, coupled phases, topology or measured original V2 optimum'}


def run():
    return {'derivative':derivative_identity(),
            'base':restricted_global_optimum(),
            'high_switch':restricted_global_optimum(Candidate(switch_per_i2_j_per_a2=.015)),
            'near_ideal_switch':restricted_global_optimum(Candidate(switch_per_i2_j_per_a2=0.))}

if __name__=='__main__':
    print(json.dumps(run(),indent=2))
