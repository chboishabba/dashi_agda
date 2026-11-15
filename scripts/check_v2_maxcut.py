#!/usr/bin/env python3
"""Independent analytic scenario checks, NOT a hardware measurement or Agda kernel check."""
from fractions import Fraction
from math import pi
import json
from pathlib import Path

INPUT = Fraction(286)
OUTPUT = Fraction(45)
RPM = Fraction(2354)
OMEGA = 2*pi*float(RPM)/60

def partition(input_w, output_w, other_w):
    return input_w == output_w + other_w and min(input_w,output_w,other_w)>=0

def storage_required(duration_s, output_w=OUTPUT):
    return output_w * duration_s

def minimum_inertia_for_fractional_speed_drop(duration_s, speed_fraction=0.99):
    # maximum rotor-energy extraction for a selected speed fall,
    # ignoring conversion loss, assuming constant J and initial speed RPM.
    return 2*float(storage_required(duration_s))/(OMEGA**2*(1-speed_fraction**2))

def findings():
    assert partition(INPUT, 0, INPUT)
    assert partition(INPUT, OUTPUT, INPUT-OUTPUT)
    assert storage_required(10) == 450
    assert storage_required(30) == 1350
    assert storage_required(60) == 2700
    assert Fraction(1,1)*OUTPUT == 45
    # Presence of pulses is not in the provided transcript.
    evidence = {'v2_pulse_topology_from_supplied_transcript':'not-established',
                'simultaneous_shaft_torque':'not-available',
                'independent_output_meter':'not-available'}
    result = {
      'provenance': 'madscience369 V2 attributed claims, supplied 90-second SRT and screenshots 2026-11-14',
      'status': 'exact scenario arithmetic only; no real apparatus calibration',
      'inputs': {'reported_input_w': '285–287 (nominal 286)', 'reported_output_w':'~45', 'reported_rpm':'2353–2354'},
      'countermodel_loss_compensation_w': {'unloaded_input':286,'unloaded_other':286,'loaded_input':286,'loaded_output':45,'loaded_other':241},
      'stored_energy_if_sustained_j': {str(t):int(storage_required(t)) for t in (10,30,60)},
      'ideal_min_rotor_inertia_1pct_speed_drop_kg_m2': {str(t):round(minimum_inertia_for_fractional_speed_drop(t),6) for t in (10,30,60)},
      'angular_speed_rad_s': round(OMEGA,6),
      'minimum_load_torque_nm':round(45/OMEGA,6),
      'evidence_gaps': evidence,
      'competing_mechanisms': ['load-dependent loss compensation','rotational energy drawdown','inductive/capacitive energy drawdown','pulsed phase selection and energy recycling','supply/ground return or other external work','meter phase, bandwidth or sign error','persistently unexplained residual'],
      'discriminator': 'synchronised all-port v(t)i(t), shaft torque(t) omega(t), shaft inertia/speed, capacitor voltage, coil current and temperatures with repeated whole-cycle endpoint matches'
    }
    return result

if __name__=='__main__':
    path=Path(__file__).resolve().parents[1]/'Artifacts/v2_finite_scenario_receipt.json'
    path.write_text(json.dumps(findings(),indent=2)+'\n')
    print(path)
    print(json.dumps(findings(),indent=2))