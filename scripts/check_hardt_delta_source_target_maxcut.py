#!/usr/bin/env python3
"""Hardt delta steelman: source inverse, target-addressability and causal gate.
All tests are mathematical/synthetic only. No biological, paranormal, or
historical physical effect is inferred. Standard-library only.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import product
from math import comb
import json

def source_nonidentifiability():
    # Uncalibrated, finite linear example; NOT a head-specific EEG/MEG model.
    sources=((Q(1),Q(0)),(Q(0),Q(1)),(Q(1,2),Q(1,2)))
    eeg=lambda x:x[0]+x[1]
    field=lambda x:x[0]-x[1]
    assert [eeg(x) for x in sources]==[1,1,1]
    assert [field(x) for x in sources]==[1,-1,0]
    for x in sources:
        e,b=eeg(x),field(x)
        assert ((e+b)/2,(e-b)/2)==x
    return {"identical_eeg_distinct_field":True,
            "projected_fields":["1","-1","0"],
            "eeg_plus_field_invertible_in_toy":True,
            "scope":"2-source linear synthetic model"}

def anonymous_target_symmetry():
    results=[]
    for n,d in ((2,12),(3,12),(4,12)):
        invariant=[]; total=0
        for pre in product(range(d+1),repeat=n-1):
            if sum(pre)>d:continue
            weights=pre+(d-sum(pre),)
            total+=1
            if all(weights[i]==weights[j] for i in range(n) for j in range(n)):
                invariant.append(weights)
        assert invariant==[(d//n,)*n]
        results.append({"receivers":n,"candidate_vectors":total,
                        "exchange_invariant":len(invariant),"each_probability":f"1/{n}"})
    return {"grid_results":results,
            "scope":"conditional exact exchangeability; real geometry or identifiable channel may break it"}

def kron_A_I(k):
    return [[k[a//2][b//2] if a%2==b%2 else Q(0)
             for b in range(4)] for a in range(4)]

def mul(a,b):
    return [[sum(a[i][k]*b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]

def transpose(a):
    return [list(row) for row in zip(*a)]

def partial_trace_A(rho):
    return [[sum(rho[2*a+i][2*a+j] for a in range(2))
             for j in range(2)] for i in range(2)]

def exact_two_qubit_no_signalling():
    # Bell Phi+ density (no irrational amplitudes required).
    rho=[[Q(0) for _ in range(4)] for _ in range(4)]
    for i in (0,3):
        for j in (0,3):rho[i][j]=Q(1,2)
    half=[[Q(1,2),Q(0)],[Q(0),Q(1,2)]]
    assert partial_trace_A(rho)==half
    # Rational amplitude-damping Kraus, parameter gamma=16/25.
    k0=[[Q(1),Q(0)],[Q(0),Q(3,5)]]
    k1=[[Q(0),Q(4,5)],[Q(0),Q(0)]]
    assert [[sum(k[t][i]*k[t][j] for k in (k0,k1) for t in range(2))
             for j in range(2)] for i in range(2)]==[[1,0],[0,1]]
    final=[[Q(0) for _ in range(4)] for _ in range(4)]
    for k in (k0,k1):
        m=kron_A_I(k)
        branch=mul(mul(m,rho),transpose(m))
        for i in range(4):
            for j in range(4):final[i][j]+=branch[i][j]
    assert partial_trace_A(final)==half
    # Conditioning on Alice's measured outcome selects distant subensembles.
    p0=[[Q(1),Q(0)],[Q(0),Q(0)]]
    p1=[[Q(0),Q(0)],[Q(0),Q(1)]]
    branches=[]
    for p in (p0,p1):
        m=kron_A_I(p)
        branches.append(partial_trace_A(mul(mul(m,rho),transpose(m))))
    assert branches==[[[Q(1,2),Q(0)],[Q(0),Q(0)]],
                      [[Q(0),Q(0)],[Q(0),Q(1,2)]]]
    assert [[sum(br[i][j] for br in branches) for j in range(2)]
            for i in range(2)]==half
    return {"local_Kraus_complete":True,
            "remote_unconditional_marginal_invariant":True,
            "conditional_subensembles_distinct":True,
            "scope":"exact rational Bell and amplitude damping INSTANCE, not general quantum kernel theorem"}

def leakage_fixture():
    rows=[(target,nuisance,nuisance,target)
          for target,nuisance in product((0,1),repeat=2)]
    blind=sum(target==receiver for target,_,receiver,_ in rows)
    leaked=sum(target==report for target,_,_,report in rows)
    assert blind==2 and leaked==4
    return {"blinded_accuracy":"1/2","leaked_report_accuracy":"1",
            "scope":"synthetic negative control, no human data"}

def randomization_fixture():
    # Hypothetical binary outcomes: 10 active (8 hits), 10 sham (3 hits).
    # Under exchangeable random allocation, 11 of 20 outcomes are hits.
    total,treated,hits,observed=20,10,11,8
    den=comb(total,treated)
    pmf={k:Q(comb(hits,k)*comb(total-hits,treated-k),den)
         for k in range(max(0,treated-(total-hits)),min(treated,hits)+1)}
    assert sum(pmf.values())==1
    p=sum((prob for k,prob in pmf.items() if k>=observed),Q(0))
    familywise=1-(1-Q(1,20))**20 # only for independent tests
    assert p==Q(293,8398)
    return {"hypothetical_active_hits":"8/10","hypothetical_sham_hits":"3/10",
            "exact_one_sided_p":str(p),"one_sided_p_approx":float(p),
            "20_independent_tests_nominal_0.05_familywise_probability":float(familywise),
            "scope":"no measured outcomes; exchangeability and independent-test assumptions explicit"}


def target_address_information_bound():
    """Fano lower bound on mutual information IF a decoder really identifies
    one of M uniformly random concealed target labels with success p.
    This is NOT Hardt's alleged 80% outcome rate or a new data observation.
    """
    from math import log2
    def entropy_bit(p):
        if p in (0.,1.):return 0.
        return -p*log2(p)-(1-p)*log2(1-p)
    m=100
    p=.8
    error=1-p
    lower=max(0.,log2(m)-entropy_bit(error)-error*log2(m-1))
    chance=1/m
    chance_bound=max(0.,log2(m)-entropy_bit(1-chance)-(1-chance)*log2(m-1))
    assert abs(chance_bound)<1e-10
    assert abs(lower-4.59605677087144)<1e-10
    return {"M":m,"assumed_concealed_target_identification_accuracy":p,
            "Fano_mutual_information_lower_bound_bits":lower,
            "chance_accuracy_bits_lower_bound":chance_bound,
            "scope":"conditional hypothetical target-label decoding; NOT the alleged 80% causal success statistic"}


def nonlinear_receiver_data_processing_cut():
    """Exact binary Markov-kernel total-variation contraction.
    For sender T -> physical arrival S -> receiver observation Y,
    a T-independent local receiver stochastic map K cannot increase
    input distinguishability; no claim that all physical processes are Markov.
    """
    grid=[Q(i,4) for i in range(5)]
    checked=0
    for s0,s1,k0,k1 in product(grid, repeat=4):
        # s_t = Pr(S=1|T=t), k_s = Pr(Y=1|S=s)
        y0=(1-s0)*k0+s0*k1
        y1=(1-s1)*k0+s1*k1
        assert y1-y0 == (s1-s0)*(k1-k0)
        assert abs(y1-y0) <= abs(s1-s0)
        if s0==s1:
            assert y0==y1
        checked+=1
    assert checked==625
    return {"rational_markov_kernel_cases":checked,
            "receiver_TV_no_greater_than_field_input_TV":True,
            "zero_sender_distinguishability_stays_zero":True,
            "scope":"conditional Markov T->S->Y, no extra receiver access to T; nonlinear thresholds included as discrete kernels"}

def main():
    result={"status":"SYNTHETIC_EXACT_MATH_ONLY",
            "source_inverse":source_nonidentifiability(),
            "target_addressability":anonymous_target_symmetry(),
            "quantum":exact_two_qubit_no_signalling(),
            "leakage":leakage_fixture(),
            "randomization":randomization_fixture(),
            "target_information":target_address_information_bound(),
            "receiver_data_processing":nonlinear_receiver_data_processing_cut()}
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=="__main__":
    main()
