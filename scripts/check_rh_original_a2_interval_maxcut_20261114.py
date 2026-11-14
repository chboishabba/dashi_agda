#!/usr/bin/env python3
"""Fail-closed exact-rational interval decision for ORIGINAL selected A2:
gap = compTarget(W,rho)+localMu(W)-localDebt(W,EV)-FarExact(W,eta,n).
A positive lower interval is PASS; nonpositive upper is NO_GO;
overlap is UNRESOLVED. Inputs are UNTRUSTED until proven on the
same selected W,rho,EV and cofinal actual zero exhaustion.
"""
from fractions import Fraction as Q
import argparse,json
FIELDS=('localPositiveDebt','FarExact','compensationTargetThreshold','localMuGain')
def iv(x):
    assert len(x)==2
    a,b=Q(str(x[0])),Q(str(x[1]));assert a<=b
    return a,b
def check(obj):
    p={k:iv(obj[k]) for k in FIELDS}
    d0,d1=p['localPositiveDebt'];f0,f1=p['FarExact']
    c0,c1=p['compensationTargetThreshold'];m0,m1=p['localMuGain']
    lo=c0+m0-d1-f1;hi=c1+m1-d0-f0
    cl='STRICT_PASS_INTERVAL' if lo>0 else ('NO_GO_INTERVAL' if hi<=0 else 'UNRESOLVED')
    return {'schema':'rh-original-a2-selected-cofinal-interval-v1',
      'result':'PASS','interval_gap':[str(lo),str(hi)],
      'arithmetic_classification':cl,
      'same_W_rho_EV_n_source_verified':False,
      'actual_cofinal_zero_estimates_verified':False,
      'Lean_kernel_receipt':False,'G3_RH_closed':False}
def test():
    base={'localPositiveDebt':['1','2'],'FarExact':['-1','1'],
      'compensationTargetThreshold':['2','4'],'localMuGain':['1','3']}
    a=check(base);assert a['arithmetic_classification']=='UNRESOLVED'
    b=check(base|{'compensationTargetThreshold':['10','12']})
    assert b['arithmetic_classification']=='STRICT_PASS_INTERVAL'
    c=check(base|{'localPositiveDebt':['20','21']})
    assert c['arithmetic_classification']=='NO_GO_INTERVAL'
    d=check(base|{'FarExact':['-100','-99']})
    assert d['arithmetic_classification']=='STRICT_PASS_INTERVAL'
    return {'result':'PASS','exact_interval_cases':4,
      'overlap':a,'hypothetical_positive':b,
      'hypothetical_reverse':c,'negative_FarExact_preserved':d,
      'original_same_source_inputs_derived':False,'kernel_receipt':False}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--certificate');v=p.parse_args()
    print(json.dumps(check(json.load(open(v.certificate))) if v.certificate
      else test(),indent=2))
