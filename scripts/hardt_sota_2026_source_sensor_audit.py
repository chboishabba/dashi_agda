#!/usr/bin/env python3
"""SOTA 2026 Hardt neural/source/mediator discriminators.
All numerical forward problems are explicitly SYNTHETIC. No user or
human source traces, extraordinary events, or device calibrations.
Original source authors and version pins belong to the companion roadmap.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import product
from math import sqrt
import json


def rref(matrix):
    if not matrix:
        return [], []
    a=[[Q(x) for x in row] for row in matrix]
    cols=len(a[0]); assert all(len(row)==cols for row in a)
    pivots=[]; r=0
    for c in range(cols):
        pivot=next((j for j in range(r,len(a)) if a[j][c]),None)
        if pivot is None: continue
        a[r],a[pivot]=a[pivot],a[r]
        divisor=a[r][c]
        a[r]=[x/divisor for x in a[r]]
        for j in range(len(a)):
            if j!=r:
                scale=a[j][c]
                a[j]=[x-scale*y for x,y in zip(a[j],a[r])]
        pivots.append(c);r+=1
        if r==len(a):break
    return a,pivots


def matvec(rows,x):
    return tuple(sum((Q(a)*Q(b) for a,b in zip(row,x)),Q(0)) for row in rows)


def rowrank(rows):
    return len(rref(rows)[1]) if rows else 0


def nullbasis(rows):
    reduced,pivots=rref(rows)
    assert rows and all(len(row)==len(rows[0]) for row in rows)
    free=[j for j in range(len(rows[0])) if j not in pivots]
    vectors=[]
    for j in free:
        v=[Q(0)]*len(rows[0]);v[j]=Q(1)
        for i,p in enumerate(pivots):v[p]=-reduced[i][j]
        assert matvec(rows,v)==tuple(Q(0) for _ in rows)
        vectors.append(tuple(v))
    return vectors


def identifiable(observations, target_row):
    """Exact finite linear theorem: target identifiable iff it lies in rowspace."""
    assert observations and len(target_row)==len(observations[0])
    basis=nullbasis(observations)
    by_rank=rowrank(observations+[target_row])==rowrank(observations)
    by_kernel=all(matvec([target_row],n)==(Q(0),) for n in basis)
    assert by_rank==by_kernel
    witness=next((n for n in basis if matvec([target_row],n)!=(Q(0),)),None)
    return by_rank,witness


def joint_sensor_source_audit():
    eeg=[[1,1,0]]; opm=[[1,0,1]]
    field_target=[0,1,-1]
    other_target=[0,0,1]
    assert identifiable(eeg,field_target)[0] is False
    assert identifiable(opm,field_target)[0] is False
    joined=eeg+opm
    assert identifiable(joined,field_target)==(True,None)
    can_other,witness=identifiable(joined,other_target)
    assert not can_other and witness is not None
    assert matvec(joined,witness)==(Q(0),Q(0))
    assert matvec([other_target],witness)!=(Q(0),)
    zero=(Q(0),Q(0),Q(0))
    assert matvec(joined,zero)==matvec(joined,witness)
    assert matvec([field_target],zero)==matvec([field_target],witness)
    assert matvec([other_target],zero)!=matvec([other_target],witness)
    checks=0
    for row1 in product((-1,0,1),repeat=3):
        if not any(row1):continue
        for row2 in product((-1,0,1),repeat=3):
            if not any(row2):continue
            m=[row1,row2]
            for target in ((1,0,0),(0,1,0),(0,0,1),(1,-1,0),(0,1,-1)):
                ok,w=identifiable(m,target)
                if not ok:assert matvec(m,w)==(Q(0),Q(0))
                checks+=1
    assert checks==26*26*5
    return {"finite_models_checked":checks,
            "eeg_only_identifies_selected_field":False,
            "opm_only_identifies_selected_field":False,
            "joint_eeg_opm_identifies_selected_field":True,
            "joint_eeg_opm_does_not_identify_all_physical_fields":True,
            "remaining_kernel_witness":list(map(str,witness)),
            "scope":"exact rational synthetic source matrix, not a calibrated head model"}


def spectral_band_admission():
    delta=(Q(1,2),Q(4))
    gnome=(Q(1,20),Q(20))
    auditory=(Q(40),Q(40))
    assert gnome[0] <= delta[0] and gnome[1]>=delta[1]
    assert not (auditory[0] <= delta[1] and auditory[1]>=delta[0])
    hypothetical_asd_fT_sqrthz=Q(5)
    bandwidth=delta[1]-delta[0]
    white_noise_rms_fT=sqrt(float(hypothetical_asd_fT_sqrthz**2*bandwidth))
    difference_rms_fT=sqrt(2)*white_noise_rms_fT
    return {"delta_band_hz":["1/2","4"],
            "gnome_2026_search_overlap":True,
            "gnome_solar_axion_non_detection_tests_human_delta":False,
            "opm_2026_40_hz_SNR_claim_calibrates_delta":False,
            "hypothetical_white_sensor_ASD_fT_per_sqrtHz":"5",
            "hypothetical_single_sensor_0p5_4Hz_rms_fT":white_noise_rms_fT,
            "hypothetical_independent_difference_rms_fT":difference_rms_fT,
            "scope":"illustrative white stationary sensor noise; not source measurement or actual band calibration"}


def evidence_versions_and_units():
    old_studies=Q(17,46)
    new_studies=Q(15,46)
    new_hypotheses=Q(17,81)
    assert old_studies != new_studies != new_hypotheses
    allocations=[[3]+[1]*14,[2,2]+[1]*13]
    assert all(sum(a)==17 and len(a)==15 for a in allocations)
    return {"v2_date":"2026-05-01","v2_positive_studies":"17/46",
            "v3_date":"2026-10-09","v3_positive_studies":"15/46",
            "v3_positive_confirmatory_hypotheses":"17/81",
            "possible_distinct_hypothesis_allocations":allocations,
            "cannot_infer_mechanism_probability_from_aggregate":True,
            "scope":"study and hypothesis denominators have different estimands; author-classified outcomes"}



def phase_cycle_adversarial_design():
    """Exact 2x2 parity projection, inspired by *method*, not copied from
    Wang et al. 2026 xenon NMR apparatus. Four samples do not prove calibration.
    """
    levels=(-2,-1,0,1,2)
    orientations=tuple(product((-1,1),repeat=2))
    checked=0
    for a,b,c,d in product(levels,repeat=4):
        signal={(s,t):Q(a+b*s+c*t+d*s*t)
                for s,t in orientations}
        interaction=sum((s*t*signal[s,t] for s,t in orientations),Q(0))/4
        assert interaction==d
        checked+=1
    assert checked==625
    # If labels are scheduled to correlate with chronological drift, a
    # *zero* true interaction may appear nonzero despite exact projection.
    confounded_schedule=((-1,1),(1,-1),(-1,-1),(1,1))
    temporal_drift=tuple(range(4))
    fake=sum(Q(s*t*k) for k,(s,t) in zip(temporal_drift,confounded_schedule))/4
    assert fake==Q(1)
    # Reversal-pair plus randomized/repeated temporal blocks, blinded label
    # ordering and measured drift are needed before physical promotion.
    return {"factorial_coefficients_checked":checked,
            "orthogonal_parity_recovers_interaction":True,
            "zero_interaction_order_correlated_drift_false_signal":str(fake),
            "scope":"finite synthetic factorial phase cycle; NOT xenon apparatus replay"}


def group_independence():
    n=100
    effective={str(rho):str(Q(n,1)/(1+(n-1)*rho))
               for rho in (Q(0),Q(1,3),Q(1))}
    assert effective=={'0':'100','1/3':'50/17','1':'1'}
    return {"number_participants":n,
            "effective_sample_size_exchangeable_illustration":effective,
            "number_target_outcomes_not_known":True,
            "scope":"illustrative identical-variance ICC correlation model, NOT observed 100-person cohort"}


def main():
    out={"status":"EXACT_SYNTHETIC_SOTA_ONLY",
         "source_observability":joint_sensor_source_audit(),
         "frequency_calibration":spectral_band_admission(),
         "versioned_evidence":evidence_versions_and_units(),
         "group_denominator":group_independence(),
         "phase_cycling":phase_cycle_adversarial_design()}
    print(json.dumps(out,indent=2,sort_keys=True))


if __name__=='__main__':main()
