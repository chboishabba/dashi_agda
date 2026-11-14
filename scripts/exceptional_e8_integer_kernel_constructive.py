#!/usr/bin/env python3
from __future__ import annotations

import json
import numpy as np
import sympy as sp

P=3
U=np.array([[1,2,0,0,0,1,0,1],[0,0,2,2,1,2,1,0],[2,2,2,1,0,1,0,0],[0,1,0,1,1,0,0,0]],dtype=int)
R=np.array([[0,1,2,2],[2,1,2,2],[2,0,2,1],[1,2,1,2],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]],dtype=int)
B=np.array([
 [0,0,0,0,0,1,2,0],
 [0,0,0,0,0,0,1,0],
 [0,0,0,0,1,2,0,0],
 [0,0,0,0,1,0,0,2],
 [0,0,0,0,0,0,0,0],
 [0,0,0,0,0,0,0,0],
 [0,0,0,0,0,0,0,0],
 [0,0,0,0,0,0,0,0]],dtype=int)
C=np.array([
 [1,-1,0,0,0,1,0,1],
 [-1,0,-1,1,0,1,1,2],
 [-2,-2,0,1,1,1,1,3],
 [-1,-2,-1,2,1,1,1,2],
 [-1,-1,-1,0,2,1,1,2],
 [-1,-1,0,0,0,2,1,1],
 [0,-1,0,0,0,0,2,1],
 [-1,-1,-1,1,0,1,0,3]],dtype=int)

def compute_receipt():
    edges=((0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(2,7))
    G=sp.eye(8)*2
    for i,j in edges:G[i,j]=G[j,i]=-1
    I=sp.eye(8)
    refs=[]
    for i in range(8):
        e=sp.zeros(8,1);e[i]=1
        refs.append(I-e*G.row(i))
    c=I
    for s in refs:c=s*c
    w=c**10
    A=np.array((I-w).tolist(),dtype=int)
    mod_split=np.array_equal((A@B)%3,(np.eye(8,dtype=int)-R@U)%3)
    triple_lift=np.array_equal(A@C,3*np.eye(8,dtype=int))
    kills=np.array_equal((U@A)%3,np.zeros((4,8),dtype=int))
    assert mod_split and triple_lift and kills
    # randomized constructive sanity checks
    rng=np.random.default_rng(20261007)
    checks=0
    for _ in range(1000):
        x=rng.integers(-20,21,size=8,dtype=int)
        if np.any((U@x)%3):
            continue
        xb=x%3
        z0=B@xb
        residual=x-A@z0
        assert np.all(residual%3==0)
        t=residual//3
        z=z0+C@t
        assert np.array_equal(A@z,x)
        checks+=1
    return {
      "u_kills_one_minus_w_mod3":kills,
      "mod3_split_identity_A_B_equals_I_minus_R_U":mod_split,
      "integer_triple_lift_A_C_equals_3I":triple_lift,
      "constructive_kernel_backsolve_checks":checks,
      "constructive_kernel_inclusion_closed":True,
      "image_into_kernel_closed":True,
      "integer_kernel_equals_image_constructively":True,
      "B":B.tolist(),"C":C.tolist()
    }

if __name__=='__main__':
    print(json.dumps(compute_receipt(),indent=2,sort_keys=True))
