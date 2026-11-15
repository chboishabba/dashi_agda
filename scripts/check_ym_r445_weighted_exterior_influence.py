#!/usr/bin/env python3
"""R445 exact finite exterior-influence control (NOT a Wilson estimate).

For P,Q>0 on finite XxY and conditional kernels K_P,K_Q:
  A = E_(P_Y) TV(K_P(.|Y), K_Q(.|Y)).
For every coupling pi of P_Y,Q_Y:
  TV(P_X,Q_X) <= A + E_pi TV(K_Q(.|Y),K_Q(.|Y')).
If Y is a product of sites, pointwise influence constants c_i give
  TV(P_X,Q_X) <= A + sum_i c_i pi(Y_i != Y'_i).
The latter follows by replacing differing coordinates sequentially.
This is exact conditional-mixture algebra, NOT physical D_k control.
"""
from fractions import Fraction as Q
from itertools import product
import json

def tv(a,b):
    assert sum(a)==sum(b)==1
    return sum((abs(x-y) for x,y in zip(a,b)),Q(0))/2

def data(weights):
    nx,ny=len(weights),len(weights[0])
    z=sum(sum(r) for r in weights)
    joint=[[Q(weights[x][y],z) for y in range(ny)] for x in range(nx)]
    py=[sum(joint[x][y] for x in range(nx)) for y in range(ny)]
    px=[sum(joint[x][y] for y in range(ny)) for x in range(nx)]
    kernels=[[joint[x][y]/py[y] for x in range(nx)] for y in range(ny)]
    return px,py,kernels

def bound(P,QW):
    px,py,kp=data(P)
    qx,qy,kq=data(QW)
    alpha=sum((py[y]*tv(kp[y],kq[y]) for y in range(len(py))),Q(0))
    kappa=max((tv(u,v) for u in kq for v in kq),default=Q(0))
    exterior=tv(py,qy)
    actual=tv(px,qx)
    assert actual<=alpha+kappa*exterior
    return actual,alpha,kappa,exterior

def weighted_far_example():
    # Exterior Y=(near,far). Change far almost maximally, keep near.
    # Both conditional kernels depend on near alone, not on far.
    qy=[Q(99,200),Q(1,200),Q(99,200),Q(1,200)]
    py=[Q(1,200),Q(99,200),Q(1,200),Q(99,200)]
    kq=[[Q(3,4),Q(1,4)],[Q(3,4),Q(1,4)],
        [Q(1,4),Q(3,4)],[Q(1,4),Q(3,4)]]
    P=[[py[y]*kq[y][x] for y in range(4)] for x in range(2)]
    R=[[qy[y]*kq[y][x] for y in range(4)] for x in range(2)]
    actual,alpha,kappa,ext=bound(P,R)
    assert actual==alpha==0 and ext==Q(49,50) and kappa==Q(1,2)
    # An explicit coupling keeps near bits equal, and flips far bits.
    near_mismatch=Q(0)
    far_mismatch=Q(49,50)
    near_influence=Q(1,2)
    far_influence=Q(0)
    weighted=near_influence*near_mismatch+far_influence*far_mismatch
    assert weighted==0
    return {'actual_local_tv':str(actual),'conditional_error':str(alpha),
            'whole_exterior_tv':str(ext),'diameter_kappa':str(kappa),
            'coarse_exterior_error':str(kappa*ext),
            'weighted_exterior_error':str(weighted)}

def check():
    cases=0
    strict=0
    weights=list(product((1,2,3),repeat=4))
    for p in weights:
        pmat=[[p[0],p[1]],[p[2],p[3]]]
        for q in weights:
            qmat=[[q[0],q[1]],[q[2],q[3]]]
            actual,alpha,kappa,ext=bound(pmat,qmat)
            assert 0<=kappa<=1
            if kappa<1 and ext>0: strict+=1
            cases+=1
    return {'schema':'ym-r445-weighted-exterior-influence-v1',
            'result':'PASS','exact_positive_2x2_pairs':cases,
            'strictly_improved_dobrushin_cases':strict,
            'far_only_case':weighted_far_example(),
            'actual_Wilson_influence_proved':False,
            'actual_D_k_proved':False,
            'Agda_kernel_receipt':False}

if __name__=='__main__':
    print(json.dumps(check(),indent=2))
