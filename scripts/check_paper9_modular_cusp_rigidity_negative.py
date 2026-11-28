#!/usr/bin/env python3
"""Exact q-series negative control: modular invariant + cusp zero != global zero.

1/j is modular invariant where defined, nonzero, and vanishes at infinity.
Its poles at elliptic j=0 prevent a holomorphic global rigidity conclusion.
This formal coefficient check is not a Bishop analytical proof.
"""
import argparse, json

def mul(a,b,N):
    c=[0]*(N+1)
    for i,x in enumerate(a[:N+1]):
        for j,y in enumerate(b[:N+1-i]): c[i+j]+=x*y
    return c

def div(a,b,N):
    assert b[0]==1
    c=[]
    for i in range(N+1): c.append(a[i]-sum(c[j]*b[i-j] for j in range(i)))
    return c

def run(N):
    sig3=[0]*(N+3); sig5=[0]*(N+3)
    for d in range(1,N+3):
        for k in range(d,N+3,d): sig3[k]+=d**3; sig5[k]+=d**5
    e4=[1]+[240*sig3[k] for k in range(1,N+3)]
    e6=[1]+[-504*sig5[k] for k in range(1,N+3)]
    M=N+1
    e4c=mul(mul(e4,e4,M),e4,M)
    e6s=mul(e6,e6,M)
    delta=[(e4c[i]-e6s[i])//1728 for i in range(M+1)]
    assert all((e4c[i]-e6s[i])%1728==0 for i in range(M+1))
    assert delta[0]==0 and delta[1]==1
    invj=div(delta,e4c,M)
    assert invj[0]==0 and invj[1]==1 and invj[2]==-744
    assert mul(invj,e4c,M)==delta[:M+1]
    return {"degree":N,"inv_j_order":1,"first_coefficients":invj[:min(8,N+2)],
        "formal_product_exact":True,"cusp_zero":True,"nonzero_germ":True,
        "globally_holomorphic_on_modular_curve":False,
        "missing_global_weld":"actual holomorphic/pole-free modular residual + compact cusp extension/rigidity"}

if __name__=="__main__":
    ap=argparse.ArgumentParser();ap.add_argument("--degree",type=int,default=80)
    a=ap.parse_args();assert 5<=a.degree<=1024
    print(json.dumps(run(a.degree),sort_keys=True))
