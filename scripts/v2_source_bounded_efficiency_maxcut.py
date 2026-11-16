#!/usr/bin/env python3
"""Source-bounded, common-shaft-power V2 *hypothesis* comparison.

The original @madscience369 V2 reel identifies NO winding/switch schematic,
shaft torque, flux-linkage map, auxiliary input or same-window storage change.
Only its reported approximate 2354 RPM is borrowed as a numerical setting.
All other circuit, nonlinear material and converter values are invented and
explicitly conditional. Original Smith/Filsinger/Resonate369 authorship is
preserved; mathematical reuse does not identify their apparatus with V2.

A single saturating, reversible winding models the strictly scoped physics:
 W'(theta,I) = .5*L0*I^2 + A*cos(k*theta)*Is^2*logcosh(I/Is),
 lambda = L0*I + A*cos(k*theta)*Is*tanh(I/Is),
 U=I*lambda-W', tau= -A*k*Is^2*logcosh(I/Is)*sin(k*theta).
L0>A>0 makes the differential inductance positive for all currents/theta.

Instantaneous rectangular current is a restricted limiting model, NOT a
finite-slew/controller voltage certificate. Switching jumps incur separately
specified energy and require a real circuit before hardware admission.
"""
from __future__ import annotations
from dataclasses import dataclass, asdict
import json
import math
from pathlib import Path
from typing import Iterable


@dataclass(frozen=True)
class Machine:
    rpm: float = 2354.0
    shaft_power_w: float = 45.0       # HYPOTHETICAL FIXED SHAFT extraction; not measured V2 shaft
    mean_inductance_h: float = .040
    varying_inductance_h: float = .012
    pole_harmonic: int = 4
    sat_current_a: float = 5.0
    resistance_ohm: float = 1.0
    peak_current_limit_a: float = 8.0
    eta_fwd: float = .98
    eta_running_regen: float = .98
    eta_clamp_basic: float = .80 # ordinary diode/rectifier recovery is not zero!
    eta_clamp_recovered: float = .95 # optional enhanced recovery path
    switch_fixed_j: float = .002
    switch_per_i2_j: float = .00015
    pulse_logic_w: float = .20       # incremental controller power when timing optimised
    recovery_controller_w: float = .40
    soft_switch_fraction: float = .80 # switch-event loss multiplier with recovery path
    core_loss_w: float = .50

    @property
    def omega(self)->float:
        return 2*math.pi*self.rpm/60.0

    def validate(self)->None:
        if not (self.mean_inductance_h>self.varying_inductance_h>0):
            raise ValueError('incremental inductance must remain positive')
        for x in (self.rpm,self.shaft_power_w,self.sat_current_a,self.resistance_ohm,
                  self.peak_current_limit_a):
            if x<=0:raise ValueError('physical benchmark requires positive parameter')
        if not isinstance(self.pole_harmonic,int) or self.pole_harmonic<=0:
            raise ValueError('positive integer rotor harmonic required')
        if not all(0<y<=1 for y in (self.eta_fwd,self.eta_running_regen,
                                   self.eta_clamp_basic,self.eta_clamp_recovered,self.soft_switch_fraction)):
            raise ValueError('converter and soft-switch fractions lie in (0,1]')
        if min(self.switch_fixed_j,self.switch_per_i2_j,self.pulse_logic_w,
               self.recovery_controller_w,self.core_loss_w)<0:
            raise ValueError('nonnegative loss parameters required')
        if self.peak_current_limit_a<1e-12:
            raise ValueError('nonzero current limit')


def logcosh(x:float)->float:
    a=abs(x)
    if a<18.:return math.log(math.cosh(a))
    return a+math.log1p(math.exp(-2*a))-math.log(2.)


def inverse_logcosh(y:float)->float:
    if y<0:raise ValueError('nonnegative logcosh required')
    if y<350:return math.acosh(math.exp(y))
    return y+math.log(2.) # large-y asymptotic for overflow prevention


def coenergy(m:Machine, x:float, i:float)->float:
    return .5*m.mean_inductance_h*i*i + m.varying_inductance_h*math.cos(x)*m.sat_current_a**2*logcosh(i/m.sat_current_a)


def flux(m:Machine,x:float,i:float)->float:
    return m.mean_inductance_h*i + m.varying_inductance_h*math.cos(x)*m.sat_current_a*math.tanh(i/m.sat_current_a)


def stored(m:Machine,x:float,i:float)->float:
    return i*flux(m,x,i)-coenergy(m,x,i)


def q_limit(m:Machine)->float:
    m.validate()
    pref=m.varying_inductance_h*m.pole_harmonic*m.omega*m.sat_current_a**2/math.pi
    capacity=pref*logcosh(m.peak_current_limit_a/m.sat_current_a)
    if m.shaft_power_w>capacity+1e-12:
        raise ValueError('specified shaft power unattainable within peak-current limit')
    return math.sqrt(max(0.,1.-(m.shaft_power_w/capacity)**2))


def current_at_fixed_shaft(m:Machine,q:float)->float:
    maxq=q_limit(m)
    if not (0<=q<=maxq+1e-13 and q<1):
        raise ValueError('pulse window exceeds fixed-shaft-power current limit')
    t=m.shaft_power_w*math.pi/(m.varying_inductance_h*m.pole_harmonic*m.omega
                              *m.sat_current_a**2*math.sqrt(1.-q*q))
    i=m.sat_current_a*inverse_logcosh(t)
    if i>m.peak_current_limit_a+1e-8:
        raise ValueError('peak current infeasible')
    return i


def positive_running_port(m:Machine,q:float,i:float)->tuple[float,float,float]:
    """Exact positive/negative part integrals of terminal instantaneous vi.

    While active on sin x>q, vi=R i^2-A*k*omega*i*Is*tanh(i/Is)sin x.
    Max/min splits integrate analytically on [asin(q),pi-asin(q)].
    The turn-on and turn-off stored energies are accounted separately.
    """
    a=math.asin(q)
    C=m.resistance_ohm*i*i
    B=m.varying_inductance_h*m.pole_harmonic*m.omega*i*m.sat_current_a*math.tanh(i/m.sat_current_a)
    total=(C*(math.pi-2*a)-2*B*math.cos(a))/(2*math.pi)
    r=C/B
    if r<=q:
        positive=0.
    elif r>=1.:
        positive=max(0.,total)
    else:
        b=math.asin(r)
        positive=max(0.,(C*(b-a)+B*(math.cos(b)-math.cos(a)))/math.pi)
    negative=max(0.,positive-total)
    return positive,negative,total


def arm(m:Machine,q:float,*,timed:bool,recovery:bool)->dict:
    """All arms share SAME shaft work, rotor, magnetic map, current ceiling.

    Ordinary control already has a competent baseline diode/rectifier clamp.
    Enhanced recovery increases the fraction returning to the useful bus. It does not change the running regenerative
    converter efficiency; extra recovery/logic power is charged. Standby/core
    loss is held fixed, with no assumptions of source-specific hardware.
    """
    m.validate()
    i=current_at_fixed_shaft(m,q)
    a=math.asin(q)
    xon=a; xoff=math.pi-a
    ev=m.pole_harmonic*m.rpm/60.0
    off_energy=stored(m,xoff,i)
    on_energy=stored(m,xon,i)
    assert min(on_energy,off_energy)>=-1e-10
    running_pos,running_neg,running_signed=positive_running_port(m,q,i)
    on_drive=ev*on_energy
    off_available=ev*off_energy
    gross_drive=on_drive+running_pos
    recoverable=running_neg+off_available
    duty=math.acos(q)/math.pi
    copper=m.resistance_ohm*i*i*duty
    shaft_from_torque=(m.varying_inductance_h*m.pole_harmonic*m.omega*m.sat_current_a**2
                       *logcosh(i/m.sat_current_a)*math.sqrt(1-q*q)/math.pi)
    ideal_export=recoverable-gross_drive
    assert math.isclose(ideal_export,shaft_from_torque-copper,rel_tol=1e-9,abs_tol=1e-9),(
        q,ideal_export,shaft_from_torque,copper,gross_drive,recoverable)
    switch=(2*ev)*(m.switch_fixed_j+m.switch_per_i2_j*i*i)
    switch*=m.soft_switch_fraction if recovery else 1.0
    pulse_logic=m.pulse_logic_w if timed else 0.
    recovery_logic=m.recovery_controller_w if recovery else 0.
    forward_loss=(1/m.eta_fwd-1)*gross_drive
    running_loss=(1-m.eta_running_regen)*running_neg
    clamp_eta=m.eta_clamp_recovered if recovery else m.eta_clamp_basic
    clamp_dump=(1-clamp_eta)*off_available
    irreversible_losses=dict(copper_w=copper,forward_converter_w=forward_loss,
        running_converter_w=running_loss,off_clamp_dump_w=clamp_dump,
        switching_w=switch,pulse_logic_w=pulse_logic,recovery_logic_w=recovery_logic,
        core_w=m.core_loss_w)
    loss_total=sum(irreversible_losses.values())
    useful=shaft_from_torque-loss_total
    # Independent port calculation, not just subtraction-based construction.
    bus_calculated=(m.eta_running_regen*running_neg
                    +(clamp_eta*off_available)
                    -gross_drive/m.eta_fwd-switch-pulse_logic-recovery_logic-m.core_loss_w)
    assert math.isclose(bus_calculated,useful,rel_tol=1e-9,abs_tol=1e-9)
    return dict(q=q,peak_current_a=i,duty_fraction=duty,mechanical_input_w=shaft_from_torque,
        terminal_gross_drive_w=gross_drive,terminal_gross_recovery_available_w=recoverable,
        running_regen_available_w=running_neg,off_clamp_available_w=off_available,
        recovered_clamp_w=clamp_eta*off_available,
        off_clamp_dump_w=clamp_dump,
        useful_bus_w=bus_calculated,losses_w=irreversible_losses,
        total_losses_w=loss_total,storage_delta_j_per_rev=0.,
        storage_scope='Only this ideal winding starts/ends at zero current; no DC-bus, battery, thermal or hysteresis endpoint certificate',
        same_shaft_w=abs(shaft_from_torque-m.shaft_power_w)<1e-9,
        accounting_residual_w=shaft_from_torque-loss_total-bus_calculated,
        timed_control=timed,clamp_recovery_enabled=recovery,
        admissible_at_assumed_peak_current=i<=m.peak_current_limit_a+1e-8,
        model_limitations='ideal rectangular current, no real slew/voltage/thermal certificate, source hardware unknown')


def search_timing(m:Machine,*,recovery:bool)->dict:
    """Restricted numerical search, not a global continuous optimum theorem."""
    maxq=q_limit(m)
    # Uniform finite grid, include both bounds. Avoid asymptote q->1.
    n=201
    rows=[arm(m, maxq*j/(n-1),timed=True,recovery=recovery) for j in range(n)]
    best=max(rows,key=lambda r:r['useful_bus_w'])
    # Local bounded refinement only improves the grid; not globally certified.
    try:
        from scipy.optimize import minimize_scalar
        from dataclasses import replace
        def f(q):return -arm(m,float(q),timed=True,recovery=recovery)['useful_bus_w']
        for j in range(1,n-1):
            if rows[j]['useful_bus_w']>=rows[j-1]['useful_bus_w'] and rows[j]['useful_bus_w']>=rows[j+1]['useful_bus_w']:
                lb=max(0.,maxq*(j-1)/(n-1)); ub=min(maxq,maxq*(j+1)/(n-1))
                res=minimize_scalar(f,bounds=(lb,ub),method='bounded',options={'xatol':1e-12})
                if res.success:
                    candidate=arm(m,float(res.x),timed=True,recovery=recovery)
                    if candidate['useful_bus_w']>best['useful_bus_w']:best=candidate
    except ImportError:
        pass
    return best


def comparison(m:Machine)->dict:
    a=arm(m,0.,timed=False,recovery=False)
    b=search_timing(m,recovery=False)
    c=arm(m,0.,timed=False,recovery=True)
    d=search_timing(m,recovery=True)
    rows={'ordinary_loading':a,'pulse_timing_only':b,
          'recovery_only':c,'combined_pulsing_and_recovery':d}
    for r in rows.values():
        assert r['same_shaft_w'] and abs(r['accounting_residual_w'])<1e-8
        assert r['storage_delta_j_per_rev']==0.
    improvements={name:row['useful_bus_w']-a['useful_bus_w']
                  for name,row in rows.items()}
    interaction=d['useful_bus_w']-b['useful_bus_w']-c['useful_bus_w']+a['useful_bus_w']
    return dict(scenario='constructed saturating magnetic winding, not original V2',
       common_shaft_power_w=m.shaft_power_w,source_reported_rpm_only=m.rpm,
       machine=asdict(m),results=rows,
       difference_from_ordinary_w=improvements,
       timing_recovery_interaction_w=interaction,
       four_way_not_same_as_loaded_unloaded='yes: all arms are under electrical load and equal shaft extraction',
       energy_limit_all_arms='useful_bus <= shaft input if nonnegative losses and zero auxiliary input',
       model_limitations=['instantaneous rectangular transitions require unbounded pulse voltage',
           'source-netlist unknown; assumes lossless recovery is possible except accounted overhead',
           'zero winding stored-energy change by construction is not whole-system storage closure',
           'fixed invented reluctance map and shaft work, no measured V2 torque',
           'real waveguide delay/FEA not used unless edge/bandwidth physically requires it'])


def load_intervention_requirement(*,output_loaded_w:float=45.,
                                  displayed_input_unloaded_w:float=286.,
                                  displayed_input_loaded_w:float=286.,
                                  delta_auxiliary_w:float=0.,
                                  delta_storage_rate_w:float=0.,
                                  delta_other_load_w:float=0.,
                                  delta_unaccounted_input_w:float=0.)->dict:
    """Whole boundary steady loaded minus unloaded conservation discriminator.

    Δload = ΔP_motor+ΔP_aux+ΔP_unaccounted-ΔP_losses-Δstorage-Δotherload.
    Δlosses is signed: negative denotes reduction under load. Inputs shown in
    the reel have NOT been calibrated against these exact input terms.
    """
    loss_delta=(displayed_input_loaded_w-displayed_input_unloaded_w
                +delta_auxiliary_w+delta_unaccounted_input_w
                -delta_storage_rate_w-delta_other_load_w-output_loaded_w)
    return dict(output_delta_w=output_loaded_w,
                motor_display_delta_w=displayed_input_loaded_w-displayed_input_unloaded_w,
                auxiliary_delta_w=delta_auxiliary_w,
                storage_rate_delta_w=delta_storage_rate_w,
                other_load_delta_w=delta_other_load_w,
                unaccounted_input_delta_w=delta_unaccounted_input_w,
                required_loss_delta_w=loss_delta,
                possible_explanations='loss suppression, additional shaft/input work, reduced other output, stored energy depletion, meter mismatch; cannot distinguish from reel',
                important_boundary='whole motor-generator system; motor electrical input is not generator shaft input')



def reel_counterworlds()->dict:
    """Four DIFFERENT full-boundary explanations of identical coarse displays.

    They are exact conservation examples, not proposed hidden V2 circuitry.
    All display the same approximate 286 W input and 45 W loaded output.
    Positive storage change is accumulation; negative is discharge.
    """
    worlds={
        'loss_redistribution':dict(true_input_w=286.,aux_w=0.,load_w=45.,
                                   losses_w=241.,storage_rate_w=0.),
        'stored_energy_depletion':dict(true_input_w=286.,aux_w=0.,load_w=45.,
                                       losses_w=286.,storage_rate_w=-45.),
        'independent_auxiliary_source':dict(true_input_w=286.,aux_w=45.,load_w=45.,
                                            losses_w=286.,storage_rate_w=0.),
        'incomplete_motor_meter':dict(true_input_w=331.,aux_w=0.,load_w=45.,
                                      losses_w=286.,storage_rate_w=0.),
    }
    for w in worlds.values():
        w['reported_input_w']=286.
        w['closed_residual_w']=(w['true_input_w']+w['aux_w']-w['load_w']
                                -w['losses_w']-w['storage_rate_w'])
        assert w['closed_residual_w']==0.
    return dict(worlds=worlds,
       identical_reel_displays_not_identifying_mechanism=True,
       warning='Constructed conservation countermodels; NONE is identified with original V2')


def sweep()->dict:
    from dataclasses import replace
    base=Machine()
    rows=[]
    for r in (.5,1.,1.5):
        for eff in (.9,.98,1.):
            for controller_overhead in (0.,.4,5.,15.,30.):
                q=replace(base,resistance_ohm=r,eta_fwd=eff,eta_running_regen=eff,
                          recovery_controller_w=controller_overhead)
                try:
                    cp=comparison(q)
                except ValueError:
                    continue
                rows.append(dict(r_ohm=r,eta=eff,recovery_overhead_w=controller_overhead,
                                 timing_gain_w=cp['difference_from_ordinary_w']['pulse_timing_only'],
                                 recovery_gain_w=cp['difference_from_ordinary_w']['recovery_only'],
                                 combined_gain_w=cp['difference_from_ordinary_w']['combined_pulsing_and_recovery'],
                                 recovery_hurts=cp['difference_from_ordinary_w']['recovery_only']<0.,
                                 combined_beats_ordinary=cp['difference_from_ordinary_w']['combined_pulsing_and_recovery']>0.))
    return dict(rows=rows,negative_recovery_examples=sum(x['recovery_hurts'] for x in rows),
                negative_combined_examples=sum(not x['combined_beats_ordinary'] for x in rows))


def run():
    m=Machine()
    return dict(schema='dashi.v2.source-bounded-efficiency.v1',
        donor_reuse=['check_v2_pulse_nonlinear_recovery.py: falling-L and fixed shaft',
                     'check_reluctance_phase_symmetry_maxcut.py: non-privileged phase count and gross bidirectional port',
                     'v2_coupled_pulse_machine_maxcut.py: source-independent saturating energy & storage ledger',
                     'SmithFilsingerTimeIndexedTransferExact: independent timed modulation work, NOT original V2 architecture'],
        main=comparison(m),
        intervention=load_intervention_requirement(),
        nonidentifiability=reel_counterworlds(),
        sensitivity=sweep())

if __name__=='__main__':
    print(json.dumps(run(),sort_keys=True,indent=2))
