#!/usr/bin/env python3
"""Independent P0-C source-separated regenerative controls.
Becker 1972 doi:10.1038/235109a0.
Murugan et al. 2022 doi:10.1126/sciadv.abj2164.
Levin 2021 doi:10.1016/j.cell.2021.02.034.
DARPA BETR 2019 HR001119S0027.
Exact synthetic mathematical tests only; no animal or clinical replay.
"""
import json
import sympy as S

def factorial_identifiability():
    base, dev, drug, interact = S.symbols("base dev drug interact")
    x = S.Matrix([base,dev,drug,interact])
    # Untreated, device-only, device+drug. Fourth group drug-only absent.
    d3 = S.Matrix([[1,0,0,0],[1,1,0,0],[1,1,1,1]])
    d4 = S.Matrix([[1,0,0,0],[1,1,0,0],[1,0,1,0],[1,1,1,1]])
    assert d3.rank()==3 and d4.rank()==4
    assert d3*S.Matrix([0,0,1,-1]) == S.zeros(3,1)
    assert d4*S.Matrix([0,0,1,-1]) != S.zeros(4,1)
    y=d3*x
    assert S.simplify(y[2]-y[1]-drug-interact)==0
    assert S.simplify(y[1]-y[0]-dev)==0
    return {"three_arm_rank":3,"four_arm_rank":4,"parameters":4,
            "missing_identification":"drug main effect versus drug-device interaction",
            "source_is_animal_study_not_clinical_reproduction":True}

def membrane_energy():
    # Finite RC model, no data-based tissue parameter estimates.
    c,g,h = S.Rational(3,2),S.Rational(2,5),S.Rational(1,4)
    v0,u = S.Rational(1,3),S.Rational(3,7)
    vm = S.factor((c*v0/h + u/2)/(c/h+g/2))
    v1 = S.factor(2*vm-v0)
    energy=lambda v:S.factor(c*v*v/2)
    balance=S.factor(energy(v1)-energy(v0)+h*g*vm*vm-h*u*vm)
    assert balance==0 and h*g*vm*vm>0
    # Source-free control cannot output useful work without storage drawdown.
    v_off=S.factor((c*v0/h)/(c/h+g/2))
    end_off=S.factor(2*v_off-v0)
    assert S.simplify(energy(end_off)-energy(v0)+h*g*v_off*v_off)==0
    return {"exact_power_residual":"0","zero_input_storage_decay":"PASS",
            "parameters":"purely synthetic","repair_outcome_inferred":False}

def observation_separation():
    # Voltage alone cannot identify hidden tissue morphology defect.
    y_voltage=S.Matrix([[1,0]])
    y_two=S.eye(2)
    assert y_voltage.rank()==1 and y_two.rank()==2
    assert y_voltage*S.Matrix([0,1])==S.zeros(1,1)
    return {"voltage_only_instantaneous_rank":1,
            "voltage_plus_independent_tissue_readout_rank":2,
            "dynamical_observability_and_causality":"NOT ESTABLISHED"}

def run():
    result={"status":"PASS","evidence":"EXACT_SYNTHETIC_ALGEBRA_ONLY",
            "frog_intervention_design":factorial_identifiability(),
            "synthetic_membrane_rc":membrane_energy(),
            "BETR_sensor_necessity":observation_separation(),
            "original_data_replayed":False}
    print(json.dumps(result,indent=2,sort_keys=True))
    return result

if __name__=="__main__":
    run()
