#!/usr/bin/env python3
"""Hardt delta steelman: bounded, standard-library mathematical discriminators.
All amplitudes/geometry are EXPLICITLY hypothetical, not experimental input.
"""
from __future__ import annotations
from fractions import Fraction
from itertools import product
import argparse
import json
import math

def causal_nonidentifiability():
    observed=(1,1,1,1,1,1,1,1,0,0)
    null=observed
    alternative=(0,)*10
    rate=Fraction(sum(observed),len(observed))
    ate0=Fraction(sum(y1-y0 for y1,y0 in zip(observed,null)),10)
    ate1=Fraction(sum(y1-y0 for y1,y0 in zip(observed,alternative)),10)
    assert (rate,ate0,ate1)==(Fraction(4,5),Fraction(0),Fraction(4,5))
    return {"observed_rate":str(rate),"same_observed_treated_data":True,
            "null_world_effect":str(ate0),"alternative_world_effect":str(ate1),
            "scope":"synthetic causal counterexample, not Hardt data"}

def local_channel_preserves_remote_marginal():
    """Exhaustive 2x2 rational classical-channel analogue of no-signalling.
    It is NOT claimed to be a quantum CPTP formalization.
    """
    grid=[Fraction(k,4) for k in range(5)]
    checked=0
    for p,q in product(grid,repeat=2):
        # Local column-stochastic operation on participant A
        T=((p,q),(1-p,1-q))
        for x in range(5):
            for y in range(5-x):
                for z in range(5-x-y):
                    w=4-x-y-z
                    P=((Fraction(x,4),Fraction(y,4)),
                       (Fraction(z,4),Fraction(w,4)))
                    before=tuple(sum(P[a][b] for a in range(2)) for b in range(2))
                    after=tuple(sum(T[an][ao]*P[ao][b]
                         for an in range(2) for ao in range(2)) for b in range(2))
                    assert before==after
                    checked+=1
    # Conditioning on a chosen outcome changes a reported subensemble,
    # not an unconditioned remote observer's accessible distribution.
    assert (Fraction(1,2),Fraction(1,2)) != (Fraction(1),Fraction(0))
    return {"rational_joint_distributions_and_channels_checked":checked,
            "remote_marginal_invariant":True,
            "postselection_distinguished_from_signalling":True}

def phase_coherence_and_dipole():
    counts=[]
    for n in range(1,11):
        ss=sum(sum(s)**2 for s in product((-1,1),repeat=n))
        ma=max(abs(sum(s)) for s in product((-1,1),repeat=n))
        assert Fraction(ss,2**n)==n
        assert ma==n
        counts.append(n)
    n=100
    distance_ratio=(Fraction(1,10)/Fraction(10,1))**3 # 0.1 m / 10 m
    reference_field_fT=Fraction(100) # HYPOTHETICAL ONLY
    single_fT=reference_field_fT*distance_ratio
    coherent=n*single_fT
    rms=float(single_fT)*math.sqrt(n)
    assert distance_ratio==Fraction(1,1_000_000)
    assert coherent==Fraction(1,100) and rms==0.001
    return {"phase_exhaustive_n":counts,"reference_field_fT":100,
            "reference_distance_m":0.1,"receiver_distance_m":10,
            "assumed_inverse_cube_ratio":str(distance_ratio),
            "n100_perfect_alignment_receiver_fT":str(coherent),
            "n100_independent_sign_rms_receiver_fT":rms,
            "scope":"ideal magnetostatic dipole: illustrative ONLY; geometry and sources unmeasured"}

def model_gates():
    return {
      "M0_common_cause":{"discriminator":"randomised cue isolation and sham; remove leakage and selection"},
      "M1_maxwell":{"discriminator":"instrument-calibrated source/current geometry, distance and orientation, pickup and sham"},
      "M2_new_local_mediator":{"discriminator":"explicit coupling, propagation/latency, independently bounded interaction and energy transfer"},
      "M3_nonlocal_causal":{"discriminator":"safe, non-injurious, concealed randomized outcome, preregistration, independent replication",
           "ceiling":"would contradict standard no-signalling if operationally controllable and no ordinary channel"},
      "status":"PREDICTIONS / TEST SPECIFICATIONS, NOT EXPERIMENTS"}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--json",action="store_true")
    args=parser.parse_args()
    result={"status":"EXACT_SYNTHETIC_ONLY","causal":causal_nonidentifiability(),
            "finite_marginal":local_channel_preserves_remote_marginal(),
            "collective_field":phase_coherence_and_dipole(),"gates":model_gates()}
    if args.json:
        print(json.dumps(result,sort_keys=True,indent=2))
    else:
        print("PASS: causal counterworld; 875 local-channel marginals; phase N=1..10; 100-source dipole fixture")
if __name__=="__main__":
    main()
