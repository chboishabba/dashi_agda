#!/usr/bin/env python3
"""Filsinger J31 consolidated exact arithmetic / proof-status audit.

Independent check of the *recorded J30 return interval* and 26-term rational
Machin period bounds, plus symbolic 9-state/6-event block-Schur regression.
The embedded J30 source values were transcribed from GitHub PR #1537's J30
machine receipt (blob 7ddea1ef36e1602e4e113bebd5e5bb351eb31910).
If invoked from a complete dashi_agda checkout, --source-receipt authenticates
that exact JSON byte-by-byte against its Git blob and compares values. This
is NOT a new validated ODE flow nor a uniform interval existence theorem.
"""
import argparse
import hashlib
import json
import math
from fractions import Fraction as F
from pathlib import Path

GRID=10**30
SOURCE_RECEIPT_BLOB="7ddea1ef36e1602e4e113bebd5e5bb351eb31910"
SEED=[
 '-0.04585851023046709','0.0967120405698972','1.9865816276887802',
 '1.1890650910077614','2.3839347955003958','5.502919318568432',
 '-5.781120275385947','-0.7451738522543331','-1.5585226674954609'
]
GRID_INTERVALS=[
 ('-46055888162564411851954452902','-45661122705384119566303532826'),
 ('96074969969251803641862133577','97349071941841418801366643328'),
 ('1983131168833363072976714910202','1990032164370646069824859131082'),
 ('1186697729040045784297053629089','1191432539582920834544982006697'),
 ('2381895047935423602281319991519','2385974573912905199191802657272'),
 ('5502824591524301334728118726327','5503014041199404297807920262546'),
 ('-5781137842199069219191063343087','-5781102689472852227402312452058'),
 ('-754193918079976812544573100849','-736153782115212391890718611106'),
 ('-1560648527654690329289150175555','-1556396830881494078213418051184')
]
TAU_GRID=[F(57119866428905331,10**16),F(14279966607226333,2500000000000000)]

def git_blob(raw):
    return hashlib.sha1(f'blob {len(raw)}\0'.encode()+raw).hexdigest()

def bounds_atan(q,n=26):
    q=F(q)
    s=sum(((-1)**k*q**(2*k+1)/F(2*k+1) for k in range(n)),F(0))
    d=(-1)**n*q**(2*n+1)/F(2*n+1)
    return min(s,s+d), max(s,s+d)

def arithmetic_check(src=None):
    if src is not None:
        raw=Path(src).read_bytes()
        assert git_blob(raw)==SOURCE_RECEIPT_BLOB,("wrong original J30 receipt Git blob",git_blob(raw))
        obj=json.loads(raw)
        assert obj['status']=='J30_PASS_NOMINAL_SIX_EVENT_EXACT_IRRATIONAL_TAU_RETURN_ENCLOSURE_BUT_NOT_PERIODIC_FIXED_POINT'
        assert obj['final_return_grid_scale']==str(GRID)
        assert obj['final_return_state_integer_interval_grid']==[list(pair) for pair in GRID_INTERVALS]
        assert obj['initial_rational_state']==SEED
        assert obj['irrational_period']['final_16_decimal_outward_time_bracket']==list(map(str,TAU_GRID))
        assert obj['six_original_hybrid_crossings_unique'] is True
        assert obj['original_J24_six_guard_boxes_paid']==5
        assert obj['exact_periodic_fixed_point_proved'] is False
        assert obj['banach_krawczyk_self_map_proved'] is False
        assert obj['return_map_interval_jacobian_on_nonzero_ball_proved'] is False
    widths=[]
    for q,(a,b) in zip(SEED,GRID_INTERVALS):
        lo=F(int(a),GRID);hi=F(int(b),GRID);x=F(q)
        assert lo<=x<=hi
        widths.append(hi-lo)
    maxwidth=max(widths)
    assert widths.index(maxwidth)==7
    assert F('0.018')<maxwidth<F('0.0181')
    old_budget=F('8.42406e-9')
    assert maxwidth>2_000_000*old_budget
    a0,a1=bounds_atan(F(1,5));b0,b1=bounds_atan(F(1,239))
    pi_lo=16*a0-4*b1;pi_hi=16*a1-4*b0
    tau_lo=F(20,11)*pi_lo;tau_hi=F(20,11)*pi_hi
    assert 0<tau_hi-tau_lo<F(5,10**38)
    assert TAU_GRID[0]<tau_lo<tau_hi<TAU_GRID[1]
    assert TAU_GRID[1]-TAU_GRID[0]==F(1,10**16)
    return dict(source_receipt_blob_expected=SOURCE_RECEIPT_BLOB,
                original_receipt_raw_byte_verified=src is not None,
                verified_nine_recorded_return_interval_seed_inclusions=9,
                max_return_width_exact=str(maxwidth),
                max_return_width_approx=float(maxwidth),
                width_over_original_raw_defect_budget_approx=float(maxwidth/old_budget),
                tau_true_26_term_Machin_uncertainty_exact=str(tau_hi-tau_lo),
                tau_true_26_term_Machin_uncertainty_approx=float(tau_hi-tau_lo),
                tau_grid_endpoints=[str(t) for t in TAU_GRID],
                tau_grid_width_exact=str(TAU_GRID[1]-TAU_GRID[0]))

def schur_check():
    from sympy import Matrix, Rational as R, eye, zeros
    n,m=9,6
    # Exact, nontrivially coupled 9+6 rational matrix representative.
    D=Matrix(m,m,lambda i,j:R([2,-3,5,7,-11,13][i], [5,7,11,13,17,19][i]) if i==j else
             R((2*i+1)*(3*j+2)%17-8,41) if i>j else 0)
    Bt=Matrix(n,m,lambda i,j:R((11*i+7*j+3)%23-11,37))
    G=Matrix(m,n,lambda i,j:R((5*i+9*j+1)%19-9,31))
    M=Matrix.diag(*[R(k+2,k+4) for k in range(n)])
    Q=M-eye(n)
    A=Q+Bt*D.inv()*G
    J=A.row_join(Bt).col_join(G.row_join(D))
    T=eye(n).row_join(-Bt*D.inv()).col_join(zeros(m,n).row_join(eye(m)))
    assert T*J==Q.row_join(zeros(n,m)).col_join(G.row_join(D))
    assert all(D[i,j]==0 for i in range(m) for j in range(i+1,m))
    assert J.det()==D.det()*Q.det()!=0
    assert J.inv()*J==eye(n+m)
    return dict(augmented_dimension=15, guard_times=6, state_coordinates=9,
                exact_schur_block_factorisation=True,
                exact_det_identity=True, real_source_interval_Jacobian_proved=False)

def run(source_receipt=None):
    a=arithmetic_check(source_receipt)
    b=schur_check()
    return dict(status='PASS_J31_SOURCE_RECEIPT_ARITHMETIC_AND_15D_ALGEBRA_ONLY',
                nominal_exact_roots_source_receipt_count=6,
                original_J24_event_state_box_source_receipt_count=5,
                full_tau_nominal_IVP_return_enclosure_source_receipt=True,
                physical_synthetic_model_only=True,
                exact_periodic_fixed_point_proved=False,
                uniform_15D_nonzero_ball_inclusion_proved=False,
                J30_recorded_arithmetic=a,schur=b,
                local_no_ci=True,Agda_kernel=False)

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--source-receipt',type=Path,default=None)
    p.add_argument('--out',type=Path,default=None)
    args=p.parse_args()
    result=run(args.source_receipt)
    raw=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.out:
        args.out.parent.mkdir(parents=True,exist_ok=True)
        args.out.write_text(raw)
    print(raw)
