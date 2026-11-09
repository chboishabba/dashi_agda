#!/usr/bin/env python3
"""Independently recompute published IonQ normalized classical cost arithmetic.

Numbers are reported-resource estimates from Provazza et al. 2026 §IV.2
(Table 3), not invoices or a fresh independent benchmark. QPU is excluded.
"""
import json
def audit():
    # Per-structure published AWS list prices (USD per instance hour).
    p5en_eight_h200_hour=54.92
    c6i_sixtyfour_cores_hour=5.44
    previous_h200_gpu_hours=13200.
    model_training_h200_gpu_hours=4.
    normalized_afqmc_physical_core_hours=6080.
    training_dataset_physical_core_hours=600.
    new_physical_core_hours=(normalized_afqmc_physical_core_hours+
                             training_dataset_physical_core_hours)
    gpu_cost=previous_h200_gpu_hours/8*p5en_eight_h200_hour
    training_cost=model_training_h200_gpu_hours/8*p5en_eight_h200_hour
    cpu_cost=new_physical_core_hours/64*c6i_sixtyfour_cores_hour
    new_classical=training_cost+cpu_cost
    assert abs(gpu_cost-90600)<25
    assert abs(new_classical-596)<2
    # 19 hours × 1280 physical cores per full 6000-step nickel run;
    # normalize to 1500 steps by dividing by four.
    assert 19*1280/4==normalized_afqmc_physical_core_hours
    total_steps=300*20
    discarded=50*20
    retained=total_steps-discarded
    assert (total_steps,discarded,retained)==(6000,1000,5000)
    return {
      "source":"Provazza et al. arXiv:2611.08129v1 §IV.2 Table 3",
      "rate_p5en_eight_h200_usd_per_instance_hour":p5en_eight_h200_hour,
      "rate_c6i_sixtyfour_cores_usd_per_instance_hour":c6i_sixtyfour_cores_hour,
      "reported_gpu_hours_old":previous_h200_gpu_hours,
      "reported_gpu_hours_training_new":model_training_h200_gpu_hours,
      "afqmc_cpu_core_hours_normalized_new":normalized_afqmc_physical_core_hours,
      "dataset_cpu_core_hours_new":training_dataset_physical_core_hours,
      "old_classical_usd_from_list_rates":gpu_cost,
      "new_gpu_training_usd_from_list_rates":training_cost,
      "new_cpu_usd_from_list_rates":cpu_cost,
      "new_classical_usd_from_list_rates":new_classical,
      "estimated_saving_fraction":(gpu_cost-new_classical)/gpu_cost,
      "published_rounded_classical_old_usd":90600,
      "published_rounded_classical_new_usd":596,
      "time_step_hartree_inverse":.005,
      "measurement_blocks":300,
      "discard_first_measured_blocks":50,
      "retained_measured_blocks":250,
      "total_propagation_steps":6000,
      "discarded_propagation_steps":1000,
      "retained_propagation_steps":5000,
      "reference_normalization_steps":1500,
      "quantum_hardware_cost_included":False,
      "independent_compute_benchmark_performed":False,
      "independent_invoices_obtained":False
    }
if __name__=="__main__":
    print(json.dumps(audit(),indent=2))
