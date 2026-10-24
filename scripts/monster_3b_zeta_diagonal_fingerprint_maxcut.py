#!/usr/bin/env python3
"""Q(zeta3) 12+78 fingerprint with a common 729-dimensional extension.

Reuses C3CyclotomicAmplitudeAlgebraExact, Monster3BCyclotomicNormSeparationExact,
IbrahimMonster3BDiagonalKernelPaidSignGaugeCorrectionExact and
IbrahimMonster3BPhaseOrientationGaugeSnowballExact. The arithmetic is
independent of GAP and mmgroup.

Original source basis: Barraclough and Wilson, The Character Table of a
Maximal Subgroup of the Monster (2007), DOI 10.1112/S1461157000001352.
Gabriele Nebe, Symmetrizations of quadratic and Hermitian forms (2025),
DOI 10.1007/s10801-025-01399-2, constructs the degree-78 Sym² module.
The quotient orientation up to centre inversion is source-paid in prior owners.

IMPORTANT: the common-Heisenberg factor condition is an assumption when
testing this four-case 12+Sym²/dual model. It is NOT a new observed Monster
W_zeta same-object intertwiner, nor a proof from dimension alone.
"""
from itertools import product
import argparse
import json
from pathlib import Path

Z=((1,0),(0,1),(-1,-1)) # 1,zeta,zeta²; zeta²+zeta+1=0

def plus(*xs):return tuple(sum(v[i] for v in xs) for i in range(2))
def scale(n,x):return n*x[0],n*x[1]
def conjugate(x):return x[0]-x[1],-x[1]
def trace(x):return 2*x[0]-x[1]
def norm(x):return x[0]**2-x[0]*x[1]+x[1]**2

def audit():
    rows=[]
    for a,variant in product((1,2),("Sym2","dualSym2")):
        b=(2*a if variant=="Sym2" else -2*a)%3
        assert b in (1,2)
        val=plus(scale(12,Z[a]),scale(78,Z[b]))
        centre_c2=(66,0)
        centre_c6=plus(scale(-12,Z[a]),scale(78,Z[b]))
        eigenspaces={"1":0,
                     "zeta":(12 if a==1 else 0)+(78 if b==1 else 0),
                     "zeta2":(12 if a==2 else 0)+(78 if b==2 else 0)}
        # For a COMMON 729 extension psi, the diagonal kernel K=<t1*t2^epsilon>
        # acts on both psi⊗U12 and psi⊗U78 by
        #         zeta^(k+epsilon*h+a) and zeta^(k+epsilon*h+b).
        # A common kernel action of 1 forces a=b.
        witnesses=[]
        for h,k,eps in product((1,2),(0,1,2),(-1,1)):
            if (k+eps*h+a)%3==0 and (k+eps*h+b)%3==0:
                witnesses.append(dict(H_t2_exp=h,H_t1_exp=k,diagonal_sign=eps))
        common=bool(witnesses)
        assert common == (a==b) == (variant=="dualSym2")
        assert trace(val)==-90
        assert norm(val)==(8100 if common else 5292)
        rows.append(dict(phase12=a,variant78=variant,phase78=b,
                         central_C3_coefficients=val,
                         central_C3_conjugate_coefficients=conjugate(val),
                         Galois_trace=trace(val),cyclotomic_norm=norm(val),
                         central_C2_coefficients=centre_c2,
                         central_C6_coefficients=centre_c6,
                         central_C3_eigenspace_multiplicities=eigenspaces,
                         common_H729_quotient_compatible=common,
                         abstract_diagonal_phase_witnesses=witnesses))
    assert {tuple(r["central_C3_coefficients"]) for r in rows}=={
        (-78,-66),(0,90),(-12,66),(-90,-90)}
    assert {tuple(r["central_C3_coefficients"]) for r in rows
            if r["common_H729_quotient_compatible"]}=={(0,90),(-90,-90)}
    assert sorted(r["cyclotomic_norm"] for r in rows)==[5292,5292,8100,8100]
    return dict(status="exact conditional cyclotomic and diagonal compatibility PASS",
                original_source=["Barraclough and Wilson (2007)",
                                 "Gabriele Nebe (2025)"],
                repository_theorem_owners=[
                    "C3CyclotomicAmplitudeAlgebraExact",
                    "Monster3BCyclotomicNormSeparationExact",
                    "IbrahimMonster3BDiagonalKernelPaidSignGaugeCorrectionExact",
                    "IbrahimMonster3BPhaseOrientationGaugeSnowballExact"],
                initial_four_fingerprints=rows,
                conditional_same_H_extension_survivors=[
                    "90*zeta","90*zetaSquared"],
                Galois_norm_criterion=dict(mixed=5292,equal_phase=8100),
                source_selected_Monster_pair_identity_proved=False,
                historical_central_kernel_word_orientation_chosen=False,
                actual_Monster_intertwiner_proved=False)

if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--receipt",type=Path)
    args=parser.parse_args()
    encoded=json.dumps(audit(),indent=2)+"\n"
    if args.receipt:args.receipt.write_text(encoded)
    print(encoded,end="")
