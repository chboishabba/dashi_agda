#!/usr/bin/env python3
"""Finite-bus averaged-PWM negative control for the *independent* V2 steelman.

Reuses the existing DASHI coupled nonlinear magnetic-memory machine, rather
than pretending instantaneous rectangular currents are physical. This is an
averaged duty controller; it does NOT resolve semiconductor switching edges,
actual V2 topology, PWM ripple, and exact thermal/whole-bus storage closure.

The printed current targets were calibrated numerically in the same simulator
to ~45 W shaft extraction; every case independently rechecks source work.
Only approximate 2354 RPM is from the original V2 reel.
"""
from __future__ import annotations
from dataclasses import asdict,replace
import importlib.util,json,sys
from pathlib import Path

HERE=Path(__file__).resolve().parent
SPEC=importlib.util.spec_from_file_location('existing_v2_coupled_machine', HERE/'v2_coupled_pulse_machine_maxcut.py')
MOD=importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name]=MOD
SPEC.loader.exec_module(MOD)

# Calibrated mean mechanical extraction target ≈45 W. In this solver these
# different q values demand different peak reference amplitudes.
TARGETS={0.0:3.8223,0.1:4.8165,0.45:14.3862}


def simulate_arm(*,q:float,reverse_eff:float,extra_controller_w:float)->dict:
    p=replace(MOD.Machine(),warmup_revs=5,measured_revs=1,steps_per_rev=180,
              eta_reverse=reverse_eff,
              static_converter_w=MOD.Machine().static_converter_w+extra_controller_w)
    row=MOD.simulate(p,m=3,peak_a=TARGETS[q],q=q,lead=.18,
                     fixed_copper_mass=True,controller_mode='pwm_tracking')
    return dict(row,unmeasured_v2_hardware=False,simulated_pwm_average=True,
        magnetic_state_near_periodic_not_thermal_stationary=True)


def run()->dict:
    arms={
      'ordinary_loading':simulate_arm(q=0.,reverse_eff=.95,extra_controller_w=0.),
      'pulse_timing_only':simulate_arm(q=.1,reverse_eff=.95,extra_controller_w=.2),
      'recovery_only':simulate_arm(q=0.,reverse_eff=.99,extra_controller_w=.4),
      'combined_pulsing_and_recovery':simulate_arm(q=.1,reverse_eff=.99,extra_controller_w=.6),
      'over_narrow_pulse_adversary':simulate_arm(q=.45,reverse_eff=.99,extra_controller_w=.6),
    }
    for x in arms.values():
        if not(x['feasible'] and x['magnetically_periodic_2pct'] and
               abs(x['power_mechanical_extract_w']-45)<.03 and
               abs(x['bus_energy_residual_j'])<.01):
            raise AssertionError(('hard source/energy/periodicity gate failed',x))
    main={k:v for k,v in arms.items() if k!='over_narrow_pulse_adversary'}
    ordinary=main['ordinary_loading']['power_bus_w']
    improvements={k:v['power_bus_w']-ordinary for k,v in main.items()}
    return dict(schema='dashi.v2.fixed-shaft-averaged-pwm-negative-control.v1',
        model='Existing v2_coupled_pulse_machine_maxcut.py, same 3-phase invented saturating mutual+lag machine',
        scope='Finite averaged bus voltage and conditional ODE state bounds, NOT transistor-resolution PWM or V2 original',
        assumed_shaft_target_w=45.,rpm=2354.,original_hardware_identified=False,
        assumptions='η_reverse .95→.99 for all negative terminal work, +.4W recovery overhead, +.2W timing logic; different from clamp-only comparator',
        reference_amplitudes=TARGETS,arms=arms,net_gain_over_ordinary_w=improvements,
        timing_can_reduce_bus_at_matched_shaft=True,
        physical_gate_status='NO V2 source-selected winding, shaft torque, actual controller, full thermal/energy inventory',
        adverse_reason='At matched shaft input copper falls when q increases, but bus/converter/switch operating costs can outweigh it')


if __name__=='__main__':print(json.dumps(run(),indent=2,sort_keys=True))
