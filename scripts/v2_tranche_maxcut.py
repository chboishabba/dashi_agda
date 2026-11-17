#!/usr/bin/env python3
"""Disjoint A-H V2 motor-generator max-cut with shared source-bounded energy ports.

The working physics is a deliberately restricted saturated single-winding pulse
family sourced from v2_source_bounded_efficiency_maxcut. No original V2 topology,
material map, switch waveform, shaft torque or calibrated power is known. The
quantitative comparison is illustrative and does not establish physical optimality.
"""
from __future__ import annotations
import json, math
from dataclasses import asdict, dataclass, replace
from pathlib import Path
from typing import Iterable
import numpy as np
from v2_source_bounded_efficiency_maxcut import Machine, arm, q_limit, comparison, reel_counterworlds, load_intervention_requirement

@dataclass(frozen=True)
class Contract:
    shaft_w:float=45.0
    rotor_rpm:float=2354.0
    storage_rate_w:float=0.0
    support_flag:str='ideal rectangular-current winding; no full physical stationarity validation'


def preflight(m:Machine,contract:Contract)->None:
    m.validate()
    assert abs(m.shaft_power_w-contract.shaft_w)<1e-10
    assert abs(m.rpm-contract.rotor_rpm)<1e-10
    assert contract.storage_rate_w==0


def tranche_ab(m:Machine,contract:Contract,n:int=81)->dict:
    """A x B: nonlinear magnetic transduction and admissible ideal pulse placement.
    Full nonlinear model / same shaft input. Restricted q current constraint only;
    finite slew/voltage is an OPEN hardware filter, never certified by this function.
    """
    preflight(m,contract)
    qs=np.linspace(0,q_limit(m),n)
    rows=[]
    for q in qs:
        r=arm(m,float(q),timed=q>0,recovery=False)
        rows.append({k:r[k] for k in ('q','peak_current_a','mechanical_input_w','terminal_gross_drive_w','terminal_gross_recovery_available_w','useful_bus_w','total_losses_w','storage_delta_j_per_rev')})
        assert abs(r['mechanical_input_w']-contract.shaft_w)<1e-8
    best=max(rows,key=lambda r:r['useful_bus_w'])
    return dict(owner='A×B',common_contract=asdict(contract),optimum_on_finite_q_grid=best,
                rows=rows,limit='Only current-limit feasible ideal pulse family; no finite slew/voltage, no field calibration')


def tranche_cd(m:Machine,contract:Contract,n:int=81)->dict:
    """C x D: signed power, running recovery, two clamp paths, controller cost.
    The same q-grid and same shaft power make comparisons composable. No phantom
    gross power source: clamp recovery is constrained by recoverable field work.
    """
    preflight(m,contract)
    rows=[]
    for q in np.linspace(0,q_limit(m),n):
        for recovery in (False,True):
            r=arm(m,float(q),timed=q>0,recovery=recovery)
            losses=r['losses_w']
            total=sum(losses.values())
            assert abs(contract.shaft_w-r['useful_bus_w']-total)<1e-8
            assert r['recovered_clamp_w']<=r['off_clamp_available_w']+1e-8
            rows.append(dict(q=float(q),recovery=recovery,bus_w=r['useful_bus_w'],
                             gross_drive_w=r['terminal_gross_drive_w'],
                             gross_available_w=r['terminal_gross_recovery_available_w'],
                             clamp_available_w=r['off_clamp_available_w'],
                             clamp_recovered_w=r['recovered_clamp_w'],
                             logic_w=losses['pulse_logic_w']+losses['recovery_logic_w'],
                             converter_loss_w=losses['forward_converter_w']+losses['running_converter_w']+losses['off_clamp_dump_w']+losses['switching_w'],
                             total_losses_w=total))
    return dict(owner='C×D',common_contract=asdict(contract),rows=rows,
                limit='Specified average converter efficiencies, ideal hard pulse, no switch-resolved PWM')


def drivetrain(motor_input_w:float,eta_motor:float,shaft_w:float,gen_bus_w:float,
               other_motor_losses_w:float=0.0)->dict:
    """E x F full motor-to-shaft-to-load accounting (motor efficiency explicit).
    motor_input_w includes motor conversion loss; shaft_w is not another input.
    For a single generator input shaft, shaft transfer must be <= motor output.
    """
    if not (0<eta_motor<=1 and motor_input_w>=0 and shaft_w>=0):
        raise ValueError('invalid motor data')
    motor_shaft=eta_motor*motor_input_w
    if motor_shaft+1e-9<shaft_w+other_motor_losses_w:
        raise ValueError('infeasible shaft demand')
    motor_loss=motor_input_w-motor_shaft
    unused_mechanical=motor_shaft-shaft_w-other_motor_losses_w
    generator_losses=shaft_w-gen_bus_w
    if generator_losses < -1e-9:
        raise ValueError('generator exceeds shaft input without auxiliary supply')
    total_losses=motor_loss+unused_mechanical+other_motor_losses_w+generator_losses
    return dict(motor_electrical_w=motor_input_w,eta_motor=eta_motor,motor_shaft_w=motor_shaft,
                shaft_to_generator_w=shaft_w,motor_internal_loss_w=motor_loss,
                unused_shaft_or_other_load_w=unused_mechanical+other_motor_losses_w,
                generator_loss_w=generator_losses,generator_bus_w=gen_bus_w,
                full_boundary_residual_w=motor_input_w-gen_bus_w-total_losses)


def tranche_ef(m:Machine,contract:Contract,eta_motors=(.55,.75,.90))->dict:
    """E x F comparative full drivetrain; separates motor input and shaft work.
    Fixed 286-W motor meter example has 45 W shaft generator load in all arms,
    with displaced other load in the illustrative full-boundary scenario.
    """
    preflight(m,contract)
    arms=comparison(m)['results']
    rows=[]
    for eta in eta_motors:
        for name,r in arms.items():
            full=drivetrain(286.,eta,contract.shaft_w,r['useful_bus_w'])
            rows.append(dict(strategy=name,**full))
            assert abs(full['full_boundary_residual_w'])<1e-8
    return dict(owner='E×F',rows=rows,
                limit='Explicit motor-efficiency scenarios and other shaft/load losses; no observed motor characteristic or 45-W source match')



def equal_input_variable_motor_efficiency(*,electrical_input_w:float=286.,
                                         extra_shaft_w:float=45.,
                                         initial_efficiency:float=.60)->dict:
    """Same displayed/true input can hide shaft-output changes if motor eta changes.
    This is an exact constrained counterworld, not evidence V2 efficiency did.
    """
    if electrical_input_w<=0 or extra_shaft_w<0 or not (0<initial_efficiency<=1):
        raise ValueError('invalid counterworld')
    loaded_eta=initial_efficiency+extra_shaft_w/electrical_input_w
    if loaded_eta>1:raise ValueError('efficiency improvement cannot supply requested shaft rise')
    motor_loss_before=electrical_input_w*(1-initial_efficiency)
    motor_loss_after=electrical_input_w*(1-loaded_eta)
    return dict(input_before_w=electrical_input_w,input_after_w=electrical_input_w,
                shaft_before_w=electrical_input_w*initial_efficiency,
                shaft_after_w=electrical_input_w*loaded_eta,
                shaft_delta_w=extra_shaft_w,
                eta_before=initial_efficiency,eta_after=loaded_eta,
                motor_loss_before_w=motor_loss_before,
                motor_loss_after_w=motor_loss_after,
                motor_loss_reduction_w=motor_loss_before-motor_loss_after,
                inference='different motor eta at fixed input is possible, not observed in V2')

def _dominates(a,b,keys=('bus_w','copper_w','converter_loss_w')):
    # Maximum output and minimum both loss coordinates.
    av=(a['bus_w'],-a['copper_w'],-a['converter_loss_w'])
    bv=(b['bus_w'],-b['copper_w'],-b['converter_loss_w'])
    return all(x>=y-1e-10 for x,y in zip(av,bv)) and any(x>y+1e-10 for x,y in zip(av,bv))


def tranche_g(m:Machine,contract:Contract,ab:dict,cd:dict,ef:dict)->dict:
    """G: joint finite-grid, loss-resolved frontier with robust negative controls.
    This is an exhaustive search over the declared finite candidate set, NOT a
    global nonlinear optimal-control proof. Finite-slew/storage/hardware = OPEN.
    """
    preflight(m,contract)
    assert ab['common_contract']==cd['common_contract']==asdict(contract)
    rows=[]
    for x in cd['rows']:
        r=arm(m,x['q'],timed=x['q']>0,recovery=x['recovery'])
        assert abs(r['useful_bus_w']-x['bus_w'])<1e-8
        assert abs(r['total_losses_w']-x['total_losses_w'])<1e-8
        rows.append(dict(q=x['q'],recovery=x['recovery'],bus_w=x['bus_w'],
                         copper_w=r['losses_w']['copper_w'],converter_loss_w=x['converter_loss_w'],
                         controller_w=x['logic_w'],peak_current_a=r['peak_current_a'],
                         shaft_w=r['mechanical_input_w'],residual_w=r['accounting_residual_w'],
                         initial_final_winding_storage_matched=True,
                         whole_system_stationarity_certified=False,
                         finite_voltage_slew_certified=False))
    best=max(rows,key=lambda x:x['bus_w'])
    front=[x for x in rows if not any(_dominates(y,x) for y in rows if y is not x)]
    baseline=arm(m,0.,timed=False,recovery=False)
    # Three independent negative controls: high controller overhead, poor
    # converter recovery, and current-limited narrow timing.
    high=replace(m,recovery_controller_w=30.)
    high_v=arm(high,0.,timed=False,recovery=True)['useful_bus_w']
    low=replace(m,eta_clamp_recovered=.20)
    poor_v=arm(low,0.,timed=False,recovery=True)['useful_bus_w']
    return dict(owner='G',number_of_candidates=len(rows),finite_grid_pareto=front,
                best_grid_candidate=best,ordinary_bus_w=baseline['useful_bus_w'],
                best_minus_ordinary_w=best['bus_w']-baseline['useful_bus_w'],
                negative_controls={'very_high_controller_overhead_bus_w':high_v,
                                   'poor_recovery_bus_w':poor_v,
                                   'current_ceiling_q_max':q_limit(m)},
                hard_gates=['finite switching voltage/slew','whole-system storage closure',
                            'converter thermal model','fixed physical material budget',
                            'validated differential inductance and real apparatus'],
                certification='Exhaustive only over finite ideal-waveform candidate grid; no global physical Pareto certificate')


def tranche_h(m:Machine,contract:Contract,ef:dict,g:dict)->dict:
    """H: exact V2 meter non-identifiability and loss-suppression thresholds.
    Instrumented V2 evidence is missing, so this is an experimental design
    and inverse-problem rejection, not source-specific closure.
    """
    sampled=[]
    for di in (-2.,0.,2.):
        sampled.append(load_intervention_requirement(output_loaded_w=45.,
                displayed_input_unloaded_w=286.,displayed_input_loaded_w=286.+di))
    return dict(owner='H',reel_reported={'motor_display_unloaded_w_approx':286.,
                  'motor_display_loaded_w_approx':286.,'loaded_output_w_approx':45.,
                  'rotor_rpm_approx':2354.},
                required_loss_delta_if_complete_meter_and_stationary_w=[r['required_loss_delta_w'] for r in sampled],
                indistinguishable_conservation_worlds=reel_counterworlds(),
                required_instruments=['same-clock true signed motor electrical power','shaft torque and RPM',
                  'generator coil and load signed vi','all converter/auxiliary power',
                  'initial/final capacitive, magnetic, thermal and kinetic states',
                  'temperature/loss mapping under randomised load interventions'],
                cannot_source_infer=True,model_best_grid_gain_w=g['best_minus_ordinary_w'],
                motor_efficiency_counterworld=equal_input_variable_motor_efficiency())


def run(n:int=81)->dict:
    m=Machine(); c=Contract()
    a=tranche_ab(m,c,n); b=tranche_cd(m,c,n); d=tranche_ef(m,c)
    g=tranche_g(m,c,a,b,d); h=tranche_h(m,c,d,g)
    assert len(a['rows'])==n and len(b['rows'])==2*n
    return {'schema':'dashi.v2.disjoint-A-H-maxcut.v1','source':'constructed, not original V2',
            'tranches':{'AB':a,'CD':b,'EF':d,'G':g,'H':h},
            'sensitivity':sensitivity_scenarios(m,c),
            'omega':{'status':'PARTIAL: common finite waveform grid + energy and identifiability; physical endpoints open',
                     'necessary_weld':'A×B + C×D + E×F with source selected parameters, finite control and same storage endpoints'},
            'acceptance':'Model-level exhaustive finite grid only, no physical source calibration'}


def sensitivity_scenarios(m:Machine,contract:Contract)->dict:
    """Counterfactual *parameter* scenarios, each internally matched for shaft work.
    Across scenarios the material/converter assumptions differ, so their absolute
    wattages are not exchangeable. Positive gain is not assumed.
    """
    preflight(m,contract)
    cases=[]
    for resistance in (.5,1.,1.5):
        for eta in (.90,.98):
            for overhead in (.4,5.,30.):
                s=replace(m,resistance_ohm=resistance,eta_fwd=eta,
                    eta_running_regen=eta,recovery_controller_w=overhead)
                cmp=comparison(s)
                cases.append(dict(resistance_ohm=resistance,eta=eta,
                    recovery_controller_w=overhead,
                    timing_gain_w=cmp['difference_from_ordinary_w']['pulse_timing_only'],
                    recovery_gain_w=cmp['difference_from_ordinary_w']['recovery_only'],
                    combined_gain_w=cmp['difference_from_ordinary_w']['combined_pulsing_and_recovery']))
    return dict(cases=cases,positive_combined=sum(c['combined_gain_w']>0 for c in cases),
        negative_combined=sum(c['combined_gain_w']<0 for c in cases),
        message='Scenario sensitivity, not probabilistic uncertainty or hardware robustness certificate')

if __name__=='__main__':
    out=run()
    path=Path(__file__).resolve().parents[1]/'Artifacts/v2_disjoint_tranches_maxcut_20261116.json'
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    b=out['tranches']['G'];h=out['tranches']['H']
    print(json.dumps({'candidate_count':b['number_of_candidates'],'best':b['best_grid_candidate'],
                      'gain_w':b['best_minus_ordinary_w'],
                      'pareto_size':len(b['finite_grid_pareto']),
                      'loss_delta_if_stationary':h['required_loss_delta_if_complete_meter_and_stationary_w']},indent=2))

