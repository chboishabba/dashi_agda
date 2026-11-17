#!/usr/bin/env python3
"""V2 efficiency-first Omega: converter admissibility and measurement observability.

All numerical magnetic parameters are invented benchmark values. No actual V2
measurements or transistor-specific converter characteristics are assumed.
"""
from __future__ import annotations
from dataclasses import dataclass, asdict
from pathlib import Path
import json, math
import numpy as np
import sympy as sp
from v2_omega_smooth_storage_metrology_maxcut import Plant, profile

UNKNOWN = ('delta_aux_w','delta_loss_w','delta_storage_rate_w','delta_other_output_w')
# Observation y = delta_load - delta_input = aux - loss - storage - other.
BALANCE = (1,-1,-1,-1)
SENSORS = {
    'auxiliary_port':(1,0,0,0),
    'direct_calorimetry':(0,1,0,0),
    'matched_storage_endpoints':(0,0,1,0),
    'other_output_ports':(0,0,0,1),
    'combined_storage_other':(0,0,1,1),
    'duplicate_input_output_meter':BALANCE,
}


def converter_admission(*,voltage_error_v:float=0.,resistance_error_ohm:float=0.,
                        thermal_voltage_derating_v:float=0.,controller_extra_w:float=.4,
                        enhanced_eta:float=.99, ordinary_eta:float=.95,
                        peak_bus_margin_v:float=0.)->dict:
    """Necessary voltage/energy conditions for a fixed, explicitly manufactured waveform.

    This is not a sufficient condition for real semiconductor switching or current tracking.
    Positive voltage_error_v is a bound on total unmodelled voltage demand.
    """
    if min(voltage_error_v,resistance_error_ohm,thermal_voltage_derating_v,controller_extra_w,peak_bus_margin_v)<0:
        raise ValueError('negative nonideality bound')
    if not (0<ordinary_eta<=1 and 0<enhanced_eta<=1):raise ValueError('passive eta required')
    p=Plant()
    r=profile(p,0.,0.)
    vmax=r['continuous_voltage_grid_lipschitz_upper_v']
    imax=r['analytic_current_upper_a']
    demand=vmax+voltage_error_v+resistance_error_ohm*imax
    available=p.Vlim_v-thermal_voltage_derating_v
    g=r['gross_reverse_w']
    net_gain=(enhanced_eta-ordinary_eta)*g-controller_extra_w
    gain_error=abs(enhanced_eta-ordinary_eta)*r['coil_abs_power_lipschitz_upper_w_per_rad']*math.pi/p.n
    return {'scope':'necessary restrictions on constructed smooth winding only; not transistor feasibility',
            'reverse_gross_w':g,'forward_gross_w':r['gross_forward_w'],
            'required_voltage_upper_v':demand,'available_voltage_v':available,
            'nominal_voltage_headroom_v':p.Vlim_v-vmax,
            'robust_voltage_headroom_v':available-demand,
            'voltage_envelope_certified':available>=demand,
            'voltage_violation_proved':False,
            'minimum_dc_bus_v':r['continuous_dc_bus_energy_lower_j']**.5*(2/p.capacitor_f)**.5,
            'dc_bus_headroom_over_required_voltage_v':r['min_dc_bus_v']-demand-peak_bus_margin_v,
            'minimum_enhanced_eta_to_break_even':ordinary_eta+controller_extra_w/g,
            'recovery_net_gain_w':net_gain,'recovery_net_gain_interval_w':[net_gain-gain_error,net_gain+gain_error],
            'gain_certified_positive':net_gain>gain_error,
            'converter_hardware_admitted':False,
            'required_missing_evidence':['full-bridge voltage capability and duty/dead-time','switching transients',
              'actual eta map at instantaneous power and temperature','bus regulation and capacitor ESR',
              'controller and cooling power at the same electrical boundary']}


def experiment_design(extra:tuple[str,...]=('auxiliary_port','matched_storage_endpoints','other_output_ports'))->dict:
    if len(set(extra))!=len(extra) or any(x not in SENSORS for x in extra):raise ValueError('invalid sensors')
    m=sp.Matrix([BALANCE,*[SENSORS[s] for s in extra]])
    rank=int(m.rank());n=4
    null=[list(v) for v in m.nullspace()]
    return {'unknowns':UNKNOWN,'sensors':extra,'rank':rank,'nullity':n-rank,
            'loss_uniquely_identifiable': all(v[1]==0 for v in m.nullspace()),
            'all_four_unknowns_identifiable':rank==4,
            'nullspace_basis':[[str(x) for x in v] for v in null],
            'matrix':[[int(x) for x in m.row(i)] for i in range(m.rows)]}


def loss_suppression_interval(*,added_load_w:float=45.,load_error_w:float=1.,
                              input_delta_w:float=0.,input_error_w:float=2.,
                              auxiliary_delta_w:float=0.,auxiliary_error_w:float=1.,
                              storage_delta_w:float=0.,storage_error_w:float=2.,
                              other_delta_w:float=0.,other_error_w:float=1.)->dict:
    """Worst-case independent absolute error bounds; do not confuse with 95% CI."""
    errors=(load_error_w,input_error_w,auxiliary_error_w,storage_error_w,other_error_w)
    if min(errors)<0:raise ValueError('uncertainty bounds must be nonnegative')
    if added_load_w<0:raise ValueError('negative new load')
    suppression=(added_load_w-input_delta_w-auxiliary_delta_w+storage_delta_w+other_delta_w)
    # D = L - input - aux + dE/dt + other; all signs from first law.
    e=sum(errors)
    return {'nominal_required_suppression_w':suppression,
            'guaranteed_suppression_interval_w':[suppression-e,suppression+e],
            'worst_case_error_w':e,'suppression_sign_certified':suppression>e,
            'confidence':None,'assumptions':'independent bounded additive errors; all ports sampled simultaneously; same window'}


def shaft_torque_requirements(rpm:float=2354.,delta_w:float=45.,
                              sensor_abs_torque_error_nm:float=.01,
                              sensor_speed_error_rpm:float=1.)->dict:
    if not (rpm>0 and delta_w>=0 and sensor_abs_torque_error_nm>=0 and sensor_speed_error_rpm>=0):
        raise ValueError('invalid torque proposal')
    omega=2*math.pi*rpm/60
    t=delta_w/omega
    # Conservative shaft power product error, assuming torque difference bound and RPM error.
    err=omega*sensor_abs_torque_error_nm+t*2*math.pi*sensor_speed_error_rpm/60 + sensor_abs_torque_error_nm*2*math.pi*sensor_speed_error_rpm/60
    return {'delta_torque_at_fixed_speed_nm':t,'omega_rad_s':omega,
        'worst_case_power_error_w':err,'example_sensor_delta_torque_error_nm':sensor_abs_torque_error_nm,
        'example_speed_error_rpm':sensor_speed_error_rpm,
        'note':'Only applies when both electrical states share same measured RPM; instrument bounds not V2 data'}


def run():
    return {'schema':'dashi.V2.Omega.converter-observability.v1',
        'baseline':converter_admission(),
        'resistance_drift_0p1_ohm':converter_admission(resistance_error_ohm=.1),
        'voltage_headroom_1_v':converter_admission(voltage_error_v=1.),
        'high_control_overhead':converter_admission(controller_extra_w=9.),
        'three_sensor_design':experiment_design(),
        'redundant_meter_negative_control':experiment_design(('duplicate_input_output_meter',)),
        'loss_measurement_design':loss_suppression_interval(),
        'shaft_measurement_design':shaft_torque_requirements(),
        'device_identified':False,'agda_kernel_verified':False}

if __name__=='__main__':
    r=run();path=Path(__file__).resolve().parents[1]/'Artifacts/v2_omega_converter_observability_cut_20261117.json';path.parent.mkdir(exist_ok=True,parents=True)
    path.write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps({k:{q:v for q,v in x.items() if q not in ('required_missing_evidence',)} if isinstance(x,dict) else x for k,x in r.items()},indent=2))
