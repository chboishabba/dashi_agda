#!/usr/bin/env python3
"""Exact interacting binary transfer-kernel analogue of YM R445 D_k.

Boundary spins a=0 and b=1, a ferromagnetic nearest-neighbor
finite-range two-state Gibbs transfer matrix P=[[3/4,1/4],[1/4,3/4]].
The exact interior total-variation change after k bonds is (1/2)^k.

This is a nontrivial correlated *benchmark model*, not the SU(N)
Wilson conditional, original physical polymer inequality, or E1/D1.
"""
from fractions import Fraction as Q
import json

P=((Q(3,4),Q(1,4)),(Q(1,4),Q(3,4)))

def step(v):
    return tuple(sum((v[i]*P[i][j] for i in range(2)),Q(0)) for j in range(2))

def tv(v,w):
    assert sum(v)==sum(w)==1
    return sum((abs(a-b) for a,b in zip(v,w)),Q(0))/2

def check():
    left=(Q(1),Q(0)); right=(Q(0),Q(1))
    certificates=[]
    for k in range(41):
        d=tv(left,right)
        predicted=Q(1,2)**k
        assert d==predicted
        assert sum(left)==sum(right)==1
        assert left[0]-right[0]==predicted
        if k in (0,1,2,4,8,16,32,40):
            certificates.append({'distance':k,'Dk':str(d),
                'conditional_P0':str(left[0]),'conditional_Q0':str(right[0])})
        left,right=step(left),step(right)
    bounds=[]
    for k0 in range(1,31):
        upper=sum((Q(1,2)**k for k in range(k0,k0+60)),Q(0))
        exact_tail=Q(1,2)**(k0-1)
        assert upper<exact_tail
        bounds.append({'from_k':k0,'infinite_tail':str(exact_tail)})
    return {'schema':'ym-r445-exact-interacting-binary-transfer-analogue-v1',
      'result':'PASS','exact_distances':41,'exact_geometric_tails':30,
      'kernel':'[[3/4,1/4],[1/4,3/4]]','variation':'D_k=(1/2)^k',
      'summable_cutoff_tail':'sum_(j=k)^inf D_j = 2^(1-k)',
      'sample_certificates':certificates,'tail_examples':bounds[-2:],
      'actual_SU_N_Wilson_kernel_proved':False,
      'actual_original_YM_Dk_bound_proved':False,
      'cutoff_uniform_RG_proved':False,'E1_or_D1_proved':False,
      'Agda_kernel_receipt':False}
if __name__=='__main__': print(json.dumps(check(),indent=2))
