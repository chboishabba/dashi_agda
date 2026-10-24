#!/usr/bin/env python3
"""Nobel optogenetics × Hardt causal mechanism discriminator, synthetic only.

Original Nobel discovery authors: Hegemann, Nagel, Deisseroth.
Primary causal neuroscience: Liu et al 2012 DOI 10.1038/nature11028;
Ramirez et al 2013 DOI 10.1126/science.1239073.
2026 SOTA: Abdeladim, Jagadisan, Shin, Ogando, Adesnik et al.,
Nature Neuroscience DOI 10.1038/s41593-026-02350-9.
2019 illumination heat confound: Owen, Liu & Kreitzer
DOI 10.1038/s41593-019-0422-3.
This code contains no original experiment, causal inference about any
human, neuronal holography, medical intervention, or paranormal evidence.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
import json

MODELS=("opsin_neural", "ordinary_light_heating",
        "opsin_correlated_optical_artifact")

@dataclass(frozen=True)
class OpticalArm:
    opsin_expressed:int
    light_delivered:int
    downstream_blocked:int=0

def response(model:str, arm:OpticalArm):
    """Exact 0/1 toy responses; not experimental probabilities."""
    o,l,b=arm.opsin_expressed,arm.light_delivered,arm.downstream_blocked
    if model=="opsin_neural":
        return int(bool(o and l and not b))
    if model=="ordinary_light_heating":
        return int(bool(l))
    if model=="opsin_correlated_optical_artifact":
        return int(bool(o and l))
    raise ValueError(model)

def four_arm(model,blocked=0):
    return {(o,l):response(model,OpticalArm(o,l,blocked))
            for o,l in product((0,1),repeat=2)}

def difference_in_differences(cells):
    return Q(cells[1,1]-cells[1,0]-cells[0,1]+cells[0,0])

def collision_audit():
    neuron=four_arm("opsin_neural")
    heating=four_arm("ordinary_light_heating")
    pickup=four_arm("opsin_correlated_optical_artifact")
    assert neuron == pickup
    assert neuron != heating
    assert difference_in_differences(neuron)==1
    assert difference_in_differences(pickup)==1
    assert difference_in_differences(heating)==0
    # Same entire ordinary 2x2 optical trial: not proof of network
    # transfer even when the interaction is large and exact.
    contrast_broken={
        m:four_arm(m,blocked=1)[1,1] for m in MODELS}
    assert contrast_broken["opsin_neural"]==0
    assert contrast_broken["opsin_correlated_optical_artifact"]==1
    # Even this contrast works only if the 'blocked' intervention is
    # separately shown not to influence the artifact/readout directly.
    return {
      "positive_light_opsin_full_factorial_rows_identical_for_neural_and_opsin_correlated_artifact":True,
      "four_arm_opsin_neural":{f"{o},{l}":v for (o,l),v in neuron.items()},
      "four_arm_heating_only":{f"{o},{l}":v for (o,l),v in heating.items()},
      "difference_in_differences_neural":str(difference_in_differences(neuron)),
      "difference_in_differences_heat":str(difference_in_differences(heating)),
      "difference_in_differences_opsin_correlated_artifact":str(difference_in_differences(pickup)),
      "blocked_mechanisms_differ":True,
      "identified_network_transmission_from_unblocked_optics_alone":False,
      "scope":"exact binary SCM, not estimated effects or measured animal responses"}

def exhaustive_nulls():
    """A fully additive optical + expression model has zero interaction."""
    levels=tuple(map(Q,range(-3,4)))
    checked=0
    for a,b,c in product(levels,repeat=3):
        # Observations from baseline a, opsin additive b, light additive c.
        tab={(o,l):a+b*o+c*l for o,l in product((0,1),repeat=2)}
        assert difference_in_differences(tab)==0
        checked+=1
    assert checked==343
    return {"additive_control_models_checked":checked,
            "all_have_zero_did":True,
            "positive_did_alone_does_not_identify_neural_propagation":True}

def independent_channel_and_target_gate():
    # Fully independent hidden target. Observing perfect local neural
    # response still leaves target ambiguity, as in BrainIT #1121 and
    # the earlier Hardt/DMT consumer collision.
    worlds=tuple(product((0,1),repeat=4)) # opsin, light, target, cue
    observations={}
    collision=None
    for o,l,t,cue in worlds:
        projected=(o,l,response("opsin_neural",OpticalArm(o,l,0)))
        if projected in observations and observations[projected] != t:
            collision=projected
        observations.setdefault(projected,t)
    assert collision is not None
    return {"invented_fine_worlds":16,
            "perfect_local_responding_neurons_does_not_decode_independent_secret":True,
            "local_optogenetic_target_spatial_address_requires_a_light_delivery_operator":True,
            "remote_person_target_address_not_inferred":True}


def three_factor_spin_vs_opsin_discriminator():
    """Three-way effect is a gate for a declared LIGHT-DEPENDENT field receptor,
    NOT an estimate of a cryptochrome spin chemical response.
    Variables: protein/receptor expression G, local illumination L,
    local *measured* magnetic perturbation B. Binary toy only.
    """
    def third_difference(cells):
        return sum(((-1)**(3-(g+l+b)))*cells[g,l,b]
                   for g,l,b in product((0,1),repeat=3))
    opsin={(g,l,b):g*l for g,l,b in product((0,1),repeat=3)}
    spin_receptor={(g,l,b):g*l*b for g,l,b in product((0,1),repeat=3)}
    assert third_difference(opsin)==0
    assert third_difference(spin_receptor)==1
    checked=0
    # Every additive or at-most-pairwise polynomial gives zero DDD:
    # baseline+single factors+pairwise interactions, all exact integers.
    for coeffs in product((-1,0,1),repeat=7):
        a,cg,cl,cb,cgl,cgb,clb=coeffs
        null={(g,l,b):(a+cg*g+cl*l+cb*b+
                           cgl*g*l+cgb*g*b+clb*l*b)
              for g,l,b in product((0,1),repeat=3)}
        assert third_difference(null)==0
        checked+=1
    assert checked==2187
    return {
      "pure_opsin_magnetic_field_three_factor_interaction":0,
      "declared_spin_receptor_three_factor_interaction":1,
      "at_most_pairwise_exact_nulls_checked":checked,
      "three_factor_interaction_is_not_cryptochrome_specific_without_controls":True,
      "required_physical_inputs":["actual illuminated protein expression",
                                  "measured external B at original biological sample",
                                  "background RF and temperature controls",
                                  "photoluminescence/photo-current/neuronal outcome separately",
                                  "receptor genetic and spectroscopy specificity"],
      "scope":"exact invented 2x2x2 factorial; NO recombinant protein, brain, magnetoreception or human target data"}

def mechanism_manifest():
    """Do NOT coerce stimulus physics across wavelength/band/identity."""
    return {
     "opsin": {"actual_wavelength_or_2photon_physics":"REQUIRED",
               "cell_specific_opsin_expression":"REQUIRED",
               "local_photon_flux_and_target_geometry":"REQUIRED",
               "photocurrent_and_off_target_light_heat":"REQUIRED"},
     "neural": {"local_and_downstream_recordings":"REQUIRED",
                "normal_circuit_transmission_and_blocker_selectivity":"REQUIRED",
                "randomized_sham_and_express_negative":"REQUIRED"},
     "receiver": {"receiver_source_identity":"REQUIRED",
                  "actual_biophysical_transfer":"REQUIRED",
                  "external_shielding_and_source_separation":"REQUIRED"},
     "claim": {"event_denominator_and_original_witness":"MISSING",
               "unassisted_distant_delta_receiver_effect":"MISSING",
               "claim_promotion":"NOT_AUTHORIZED"},
     "source":"synthetic protocol gates, not a physical experiment"}

def main():
    print(json.dumps({"status":"SYNTHETIC_CAUSAL_MATH_ONLY",
                      "mechanism_collisions":collision_audit(),
                      "additive_null":exhaustive_nulls(),
                      "independent_secret":independent_channel_and_target_gate(),
                      "opsin_vs_spin":three_factor_spin_vs_opsin_discriminator(),
                      "experiment_gates":mechanism_manifest()},
                     sort_keys=True,indent=2))
if __name__=="__main__":
    main()
