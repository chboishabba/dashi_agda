#!/usr/bin/env python3
"""Exact rational 4D marginal-subtracted UV remainder tail.

This validates telescoping algebra, not a bound on original YM RG defects.
"""
from fractions import Fraction as Q
import json

def uv_tail(n,A,C,H):
    poly=sum((A/Q((k+1)*(k+2)) for k in range(n)),Q(0))
    irr=sum((C*Q(1,2)**(k+1) for k in range(n)),Q(0))
    holes=sum((H*Q(1,2)**(k+1) for k in range(n)),Q(0))
    assert poly==A*(1-Q(1,n+1))
    assert irr==C*(1-Q(1,2)**n)
    assert holes==H*(1-Q(1,2)**n)
    return poly+irr+holes

def selftest():
    q0,A,C,H=Q(1,4),Q(1,16),Q(1,32),Q(1,64)
    q=q0+A+C+H
    assert q==Q(23,64)<1
    depths=[1,2,4,8,16,64,256,512]
    for n in depths:
        assert uv_tail(n,A,C,H)<=A+C+H
        assert q0+uv_tail(n,A,C,H)<=q
    harmonic=sum((Q(1,k+1) for k in range(128)),Q(0))
    assert harmonic>3
    return {'status':'PASS_EXACT_RATIONAL_REFERENCE',
      'q0':str(q0),'A':str(A),'C':str(C),'H':str(H),
      'q_if_true_original_source_bounds':str(q),
      'tested_depths':depths,'harmonic_unsubtracted_negative_control':True,
      'original_Wilson_rg_error_bound':False,
      'Agda_kernel_acceptance':False,'Clay':False}

if __name__=='__main__':
    print(json.dumps(selftest(),indent=2))
