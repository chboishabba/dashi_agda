#!/usr/bin/env python3
"""Exact conditional symmetry + adversarial phase-count controls.

This is DASHI's independently constructed model, not a teardown, calibration,
or circuit disclosure by @madscience369, Slobodian/Infinity SAV, or Holmstrom.
The ideal symmetric family is a *model countercontrol*: it demonstrates that
phase-number efficiency conclusions can be artifacts of assumed overhead.
"""
from __future__ import annotations

import importlib.util
import json
import math
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    'v2_reluctance_pulse', HERE/'check_reluctance_permeance_phase_maxcut.py')
MODEL = importlib.util.module_from_spec(SPEC)
import sys
sys.modules[SPEC.name] = MODEL
SPEC.loader.exec_module(MODEL)


def exact_replicated_phase_cancellation():
    """Average of identical phase-rotated periodic waveforms; m cancels.

    Let f be any 2pi-periodic pulse shape, and A = mean f² > 0,
    B = mean(f² sin x) over one cycle. For m equal coils with L=L0+a cos x
    and fixed sum(mean(i_j²)) = S, I²=S/(m*A). Then average torque,
    copper, and net coil-port power are independent of m. The proof is
    algebraic *after* the integral-translation invariance of 2pi-periodic
    functions, not a proof about physically different machines.
    """
    m, A, B, S, R, a, h, omega = sp.symbols('m A B S R a h omega',
                                           positive=True, finite=True)
    I2 = S/(m*A)
    torque = -sp.Rational(1,2)*m*a*h*I2*B
    copper = m*R*I2*A
    shaft = -omega*torque
    electric_export = shaft-copper
    target_torque = -a*h*S*B/(2*A)
    target_copper = R*S
    assert sp.simplify(torque-target_torque)==0
    assert sp.simplify(copper-target_copper)==0
    assert sp.simplify(electric_export - (omega*a*h*S*B/(2*A)-R*S))==0
    assert m not in sp.simplify(electric_export).free_symbols

    # General conservative two-coil nonlinear coenergy including a PM bias.
    theta, i1, i2, di1, di2, w = sp.symbols(
        'theta i1 i2 di1 di2 omega', real=True)
    Wp = sp.Function('Wprime')(theta, i1, i2)
    currents=sp.Matrix([i1,i2]); rates=sp.Matrix([di1,di2])
    flux = sp.Matrix([sp.diff(Wp,i1),sp.diff(Wp,i2)])
    field_energy = (currents.T*flux)[0] - Wp
    torque = sp.diff(Wp,theta)
    electrical = (currents.T*sp.Matrix([
        sp.diff(flux[j],theta)*w+sum(sp.diff(flux[j],x)*dx for x,dx in zip((i1,i2),(di1,di2)))
        for j in range(2)]))[0]
    stored_rate=sp.diff(field_energy,theta)*w+sp.diff(field_energy,i1)*di1+sp.diff(field_energy,i2)*di2
    assert sp.simplify(electrical - stored_rate - w*torque)==0
    # This identity excludes hysteretic path dependence and any unmodelled source.
    return {
        'symbolic_phase_normalization':'m cancels for equal cyclic shifts and fixed total mean current squared',
        'mean_torque':'-a*h*S*B/(2*A)',
        'mean_copper_loss':'R*S',
        'mean_ideal_export':'omega*a*h*S*B/(2*A)-R*S',
        'nonlinear_multicoil_coenergy':'formal symbolic identity = 0',
        'conditionality':'identical periodic coil maps, equal R, lossless reversible magnetics, fixed S and pulse shape'}


def phase_penalty_thresholds():
    """Exact phase-count crossover values for ideal C_m = H_m+alpha*m."""
    h={m:MODEL.ideal_phase_cover(m)['constant_torque_current_sq_multiplier']
       for m in range(3,13)}
    edge={m: h[m]-h[m+1] for m in range(3,12)}
    assert all(edge[m]>edge[m+1]>0 for m in range(3,11))
    def interval(m):
        # At equality there are ties. The displayed values are boundaries.
        return {'alpha_lower':edge[m] if m<12 else 0.0,
                'alpha_upper':edge[m-1] if m>3 else None}
    assert interval(3)['alpha_lower'] > interval(6)['alpha_upper']
    return {'model':'ideal single-active-slope commutation, C_m=H_m+alpha*m, m in [3,12]',
            'adjacent_crossovers':{str(k):v for k,v in edge.items()},
            'phase_3':interval(3),'phase_6':interval(6),'phase_9':interval(9),
            'negative_control':'other phase counts also win on open alpha intervals'}


def assess_normalized_phase_invariance():
    m0=MODEL.Model(samples=3072)
    cases=[]
    for delta,p in ((0.,1.5),(.2,2.3),(-.15,3.0)):
        rows=[MODEL.simulate(m,delta,p,m0) for m in range(3,13)]
        for key in ('mean_electromagnetic_braking_w','copper_w',
                    'ideal_net_electrical_out_w','positive_coil_port_gross_w',
                    'negative_coil_port_gross_w'):
            vals=[x[key] for x in rows]
            # Positive-part rectification introduces a sharp zero crossing;
            # its finite-grid quadrature converges more slowly than signed power.
            tolerance = 1e-2 if key in ('positive_coil_port_gross_w',
                                         'negative_coil_port_gross_w') else 2e-3
            assert max(vals)-min(vals)<tolerance,(key,max(vals)-min(vals))
        # Not a general theorem that every greater-m machine has lower ripple;
        # discrete sampled pulse aliasing can be nonmonotonic.
        cases.append({'pulse_phase_rad':delta,'pulse_exponent':p,
                      'mean_shaft_braking_range_w':float(max(x['mean_electromagnetic_braking_w'] for x in rows)-min(x['mean_electromagnetic_braking_w'] for x in rows)),
                      'copper_spread_w':float(max(x['copper_w'] for x in rows)-min(x['copper_w'] for x in rows)),
                      'ideal_export_spread_w':float(max(x['ideal_net_electrical_out_w'] for x in rows)-min(x['ideal_net_electrical_out_w'] for x in rows)),
                      'bus_drop_3_to_9_w':float(rows[0]['realistic_bus_out_w']-rows[6]['realistic_bus_out_w']),
                      'ripple_3':float(rows[0]['torque_ripple_rms_over_mean']),
                      'ripple_6':float(rows[3]['torque_ripple_rms_over_mean']),
                      'ripple_9':float(rows[6]['torque_ripple_rms_over_mean'])})
    return {'symmetry_cases':cases,
            'phase_dependence_of_bus':'imposed m*switch_overhead; other identical-model per-cycle flow invariant'}


def ideal_regulator_sensitivity():
    """No converter losses versus bidirectional processing losses, same coil waveform."""
    base=MODEL.Model()
    rows=[]
    for eta in (0.90,0.95,0.98,0.99,1.0):
        x=MODEL.simulate(3,0.,1.5,MODEL.replace(base,eta_forward=eta,eta_reverse=eta,
                                                 switch_overhead_w_per_phase=0.))
        rows.append({'eta':eta,'bus_w':x['realistic_bus_out_w'],
                     'coil_ideal_w':x['ideal_net_electrical_out_w'],
                     'gross_drive_w':x['positive_coil_port_gross_w'],
                     'gross_recovery_w':x['negative_coil_port_gross_w']})
    assert all(rows[i]['bus_w'] < rows[i+1]['bus_w'] for i in range(len(rows)-1))
    assert math.isclose(rows[-1]['bus_w'],rows[-1]['coil_ideal_w'],abs_tol=1e-8)
    assert rows[-1]['bus_w'] <= MODEL.simulate(3,0.,1.5,base)['mean_electromagnetic_braking_w']
    return {'cases':rows,'mechanism':'large internal bidirectional coil power makes converter loss material',
            'limit':'at ideal conversion exported electric power equals shaft extraction minus copper and other modelled losses'}


def run():
    return {'schema':'dashi.reluctance.phase-symmetry-maxcut.v2',
            'author_role':'independent DASHI comparative modelling, not attributed circuit disclosure',
            'models_not_identical':['madscience369 V2','Slobodian/Infinity SAV MG10',
                                    'David Holmstrom Resonate369 devices'],
            'exact':exact_replicated_phase_cancellation(),
            'phase_overhead_thresholds':phase_penalty_thresholds(),
            'phase_model_invariance':assess_normalized_phase_invariance(),
            'regulator_efficiency':ideal_regulator_sensitivity(),
            'open_physical_producers':['V2 original selected netlist and waveform',
                'same-device flux linkage lambda(theta,i), leakage and saturation',
                'same-run torque/rotor phase/load and all real power ports',
                'signed beginning/end storage and loss uncertainty',
                'Agda pinned-kernel acceptance and continuous-voltage bound']}

if __name__=='__main__':
    result=run()
    dest=Path(__file__).resolve().parents[1]/'Artifacts/v2_phase_symmetry_maxcut_20261115.json'
    dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps({'receipt':str(dest),'exact':result['exact'],
                      'phase_overhead_thresholds':result['phase_overhead_thresholds'],
                      'symmetry_cases':result['phase_model_invariance']['symmetry_cases']},indent=2))