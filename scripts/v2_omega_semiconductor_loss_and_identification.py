#!/usr/bin/env python3
"""V2 Omega: explicit reverse-path semiconductor loss budget and measurement rank.

A conditional *design-class* loss model, not a device datasheet or V2 netlist.
The current and terminal-voltage waveforms come from the pre-existing smooth
reversible reluctance producer; all semiconductor parameters below are invented
interval-study assumptions. No hard-switched silicon, junction thermal network,
PWM tracking or actual V2 hardware is admitted. Energy units are watts/joules.
"""
from __future__ import annotations
from dataclasses import dataclass, asdict, replace
import json, math
from pathlib import Path
import numpy as np
from v2_omega_smooth_storage_metrology_maxcut import Plant, profile, shape

@dataclass(frozen=True)
class ReverseBridge:
    pwm_hz:float=20000.
    active_devices:int=2
    r_path_ohm:float=.015
    switch_e0_j:float=3e-6
    switch_e_per_a_j:float=.3e-6
    gate_charge_c:float=35e-9
    gate_drive_v:float=12.
    deadtime_s:float=150e-9
    diode_drop_v:float=.8
    controller_extra_w:float=.4
    ambient_c:float=35.
    thermal_resistance_c_per_w:float=7.
    thermal_limit_c:float=110.
    # Source-to-bridge & motor output have no unmetered supply in this model.
    def validate(self):
        vars_=asdict(self)
        if any(v<0 for k,v in vars_.items() if k not in ('ambient_c','thermal_limit_c')):
            raise ValueError('negative semiconductor parameter')
        if not (self.pwm_hz>0 and self.active_devices>=1 and
                2*self.deadtime_s*self.pwm_hz<=1 and
                self.thermal_limit_c>self.ambient_c):
            raise ValueError('invalid PWM, deadtime or temperature limits')


def magnetic_waveform(plant:Plant,q:float=0.,lead:float=-.15)->dict:
    """Reuse exact manufactured winding current/voltage and shaft normalisation."""
    ref=profile(plant,q,lead,require_feasible=False)
    x=2*math.pi*np.arange(plant.n)/plant.n
    f,df=shape(x,q,lead)
    i=ref['scale_a']*f
    wp=plant.pole_harmonic*plant.omega
    di=ref['scale_a']*wp*df
    lam_i=plant.L0_h+plant.A_h*np.cos(x)/np.cosh(i/plant.Is_a)**2
    lam_t=-plant.A_h*np.sin(x)*plant.Is_a*np.tanh(i/plant.Is_a)*wp
    v=plant.R_ohm*i+lam_i*di+lam_t
    signed=i*v
    negative=np.maximum(-signed,0.)
    positive=np.maximum(signed,0.)
    reverse=signed<0
    assert abs(float(np.mean(negative))-ref['gross_reverse_w'])<1e-8
    assert abs(float(np.mean(positive))-ref['gross_forward_w'])<1e-8
    return {'reference':ref,'i':i,'v':v,'reverse':reverse,'reverse_power':negative,
            'forward_power':positive,'period_s':2*math.pi/plant.omega}


def evaluate(bridge:ReverseBridge=ReverseBridge(),plant:Plant=Plant(n=8192),
             q:float=0.,lead:float=-.15,ordinary_eta:float=.95,
             max_required_voltage_extra_v:float=3.,voltage_derate_v:float=2.)->dict:
    bridge.validate();plant.validate()
    if not 0<ordinary_eta<=1:raise ValueError('ordinary efficiency')
    if min(max_required_voltage_extra_v,voltage_derate_v)<0:raise ValueError('negative voltage uncertainty')
    w=magnetic_waveform(plant,q,lead)
    r=w['reference'];i=w['i'];rev=w['reverse'];P=w['reverse_power']
    fraction=float(np.mean(rev))
    i2=float(np.mean(np.where(rev,i*i,0.)))
    iabs=float(np.mean(np.where(rev,np.abs(i),0.)))
    # Each cost is averaged over the whole mechanical period. Switching loss
    # here assumes reverse branch is enabled only during negative terminal power.
    conduction=bridge.r_path_ohm*i2
    switching=bridge.pwm_hz*bridge.active_devices*(bridge.switch_e0_j*fraction+
                bridge.switch_e_per_a_j*iabs)
    gate=bridge.pwm_hz*bridge.active_devices*bridge.gate_charge_c*bridge.gate_drive_v
    diode=2*bridge.deadtime_s*bridge.pwm_hz*bridge.diode_drop_v*iabs
    semiconductor_heat=conduction+switching+diode
    reverse_losses=semiconductor_heat+gate
    extra_loss=reverse_losses+bridge.controller_extra_w
    gross=float(np.mean(P))
    # Ordinary eta is an already-recovering reference, not a dump-to-heat baseline.
    original_reverse_loss=(1-ordinary_eta)*gross
    gain=original_reverse_loss-extra_loss
    effective_eta=1-reverse_losses/gross
    # The reference's other forward, bridge, copper and core losses are held
    # exactly matched; only recovery-side incremental costs differ.
    ordinary_bus=profile(plant,q,lead,eta_reverse=ordinary_eta,control_extra_w=0.,
                         require_feasible=False)['net_bus_w']
    enhanced_bus=ordinary_bus+gain
    temp=bridge.ambient_c+bridge.thermal_resistance_c_per_w*semiconductor_heat
    headroom=plant.Vlim_v-voltage_derate_v-max_required_voltage_extra_v-r['continuous_voltage_grid_lipschitz_upper_v']
    # Reconstruct periodic bus energy using a constant-power sink equal to the
    # *sampled* mean of the actual averaged signed source. No claim of exact
    # continuous integral, PWM bus ripple or capacitor ESR pass is made.
    source=w['reverse_power']-bridge.r_path_ohm*np.where(rev,i*i,0.)
    source-=2*bridge.deadtime_s*bridge.pwm_hz*bridge.diode_drop_v*np.where(rev,np.abs(i),0.)
    source-=bridge.pwm_hz*bridge.active_devices*(bridge.switch_e0_j*rev.astype(float)+
                bridge.switch_e_per_a_j*np.where(rev,np.abs(i),0.))
    source-=w['forward_power']/plant.eta_forward
    source-=(bridge.gate_charge_c*bridge.gate_drive_v*bridge.pwm_hz*bridge.active_devices+
             bridge.controller_extra_w+plant.bridge_loss_w+plant.core_loss_w+plant.control_loss_w)
    assert abs(float(np.mean(source))-enhanced_bus)<1e-7
    dt=w['period_s']/plant.n
    E0=.5*plant.capacitor_f*plant.bus_initial_v**2
    E=E0+np.r_[0.,np.cumsum((source-np.mean(source))*dt)]
    min_v=float(np.sqrt(2*min(E)/plant.capacitor_f)) if min(E)>0 else 0.
    max_v=float(np.sqrt(2*max(E)/plant.capacitor_f)) if min(E)>0 else 0.
    loss_account=conduction+switching+gate+diode+bridge.controller_extra_w
    signed_check=original_reverse_loss-loss_account-gain
    return {'schema':'DASHI.V2.Omega.semiconductor-loss-and-identification.v1',
       'source_selected':False,'bridge_assumptions':asdict(bridge),
       'scope':'Invented reverse-path averaged PWM cost model on a manufactured smooth winding waveform',
       'q':q,'lead_rad':lead,'shaft_w':r['shaft_w'],'gross_reverse_w':gross,
       'reverse_on_fraction':fraction,'reverse_i2_mean_a2':i2,'reverse_abs_i_mean_a':iabs,
       'ordinary_reverse_loss_w':original_reverse_loss,
       'conduction_loss_w':conduction,'switching_loss_w':switching,
       'gate_driver_w':gate,'deadtime_diode_w':diode,
       'semiconductor_heat_w':semiconductor_heat,'controller_extra_w':bridge.controller_extra_w,
       'enhanced_reverse_loss_w':reverse_losses,
       'implied_enhanced_reverse_eta':effective_eta,
       'recovery_gain_over_ordinary_w':gain,'ordinary_bus_w':ordinary_bus,
       'enhanced_bus_w':enhanced_bus,'signed_gain_ledger_residual_w':signed_check,
       'junction_temperature_c_lumped_upper':temp,'thermal_bound_pass':temp<=bridge.thermal_limit_c,
       'conservative_winding_voltage_headroom_v':headroom,'voltage_bound_pass':headroom>=0,
       'sampled_bus_v_min':min_v,'sampled_bus_v_max':max_v,
       'sampled_bus_energy_endpoint_residual_j':float(E[-1]-E[0]),
       'sampled_bus_range_pass':min_v>=plant.bus_min_v and max_v<=plant.bus_max_v,
       'net_gain_positive':gain>0,
       'conditional_design_budget_pass':gain>0 and temp<=bridge.thermal_limit_c and headroom>=0 and
                        min_v>=plant.bus_min_v and max_v<=plant.bus_max_v,
       'missing':['switch-node voltage/current overlap waveforms and device datasheets',
                   'actual PWM tracking at hard/soft switches and deadtime, time-resolved bus current',
                   'electrothermal junction dynamics, magnetic memory and capacitor ESR',
                   'measured V2 topology, motor shaft torque and all input/output ports']}


def sensitivity():
    base=ReverseBridge()
    choices=[('reference',base),('switch_energy_x4',replace(base,switch_e0_j=base.switch_e0_j*4,
                                                            switch_e_per_a_j=base.switch_e_per_a_j*4)),
             ('conduction_x8',replace(base,r_path_ohm=base.r_path_ohm*8)),
             ('controller_10W',replace(base,controller_extra_w=10.)),
             ('hard_switch_1mJ',replace(base,switch_e0_j=.001)),
             ('thermal_x5',replace(base,thermal_resistance_c_per_w=base.thermal_resistance_c_per_w*5)),
             ('gate_charge_x12',replace(base,gate_charge_c=base.gate_charge_c*12))]
    return {name:{k:r[k] for k in ('recovery_gain_over_ordinary_w','implied_enhanced_reverse_eta',
           'junction_temperature_c_lumped_upper','thermal_bound_pass','conditional_design_budget_pass')}
            for name,b in choices for r in [evaluate(b)]}


def run():
    nominal=evaluate()
    return {'nominal':nominal,'sensitivity':sensitivity(),
            'critical_naming':'Loss-parameter assumptions are illustrative, not identified power semiconductor devices',
            'original_v2_verification':'OPEN','agda_kernel':'NOT RUN'}

if __name__=='__main__':
    r=run();out=Path(__file__).resolve().parents[1]/'Artifacts/v2_omega_semiconductor_loss_and_identification_20261117.json'
    out.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'nominal':{k:v for k,v in r['nominal'].items() if k not in ('bridge_assumptions','missing')},'sensitivity':r['sensitivity']},indent=2))
