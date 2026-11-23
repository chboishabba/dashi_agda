#!/usr/bin/env python3
"""P1 independent structural controls, not source device or clinical evidence.

Original interfaces: DARPA N3, HI-MEMS, Insect Allies; Profusa Lumee Oxygen;
SCENAR sham-controlled PMCID PMC8658569 and PMC9917375.
Reuses repo P0-C bioelectric source/repair boundary in documentation.
No patient-level original data, no physical field simulation.
"""
import json
import sympy as S

def oxygen_delivery_consump():
    delivery,consumption=S.symbols("delivery consumption",real=True)
    readout=S.Matrix([delivery-consumption])
    jac=readout.jacobian([delivery,consumption])
    assert jac.rank()==1
    assert jac*S.Matrix([1,1])==S.zeros(1,1)
    independent=S.Matrix([delivery-consumption,delivery])
    assert independent.jacobian([delivery,consumption]).rank()==2
    return {"one_oxygen_balance_observation_rank":1,
            "delivery_and_consumption_unknowns":2,
            "independent_delivery_measurement_rank":2,
            "common_shift_null_direction":[1,1],
            "interpretation":"model structural rank only, no calibration, clinical effect or dynamic observability"}

def sensor_actuator_outcome():
    # A measurement, an actuator output and a tissue outcome have distinct
    # records; the mere coexistence of components does not supply controlled
    # causal effect or an observed physiological state transition.
    v,t=S.symbols("voltage tissue_outcome",real=True)
    only_voltage=S.Matrix([v]).jacobian([v,t])
    both=S.Matrix([v,t]).jacobian([v,t])
    assert only_voltage.rank()==1 and both.rank()==2
    return {"voltage_only_instantaneous_rank":1,
            "voltage_and_independent_outcome_rank":2,
            "integrated_closed_loop_human_device_established":False}

def type_gate():
    # These channels cannot be erased into one undifferentiated wireless
    # bioelectric mechanism simply because radio/electronics appear.
    routes={
      "N3":"neural_read_write_program_goal",
      "Profusa":"subcutaneous_tissue_oxygen_optical_readout",
      "SCENAR":"contact_skin_electrical_actuator",
      "HI_MEMS":"conventional_RF_to_insect_stimulation",
      "Insect_Allies":"insect_vectored_modified_plant_virus"
    }
    assert len(routes)==5 and len(set(routes.values()))==5
    assert routes["Insect_Allies"]!="neural_read_write_program_goal"
    return routes

def run():
    value={"status":"PASS","tier":"EXACT_SYMBOLIC_OBSERVABILITY_NOT_EMPIRICAL_REPLAY",
           "oxygen_balance":oxygen_delivery_consump(),
           "sensor_actuator_outcome":sensor_actuator_outcome(),
           "source_interface_types":type_gate()}
    print(json.dumps(value,indent=2,sort_keys=True))
    return value

if __name__=="__main__":
    run()
