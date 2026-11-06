#!/usr/bin/env python3
"""Exact rational RG charge-survival regression; no YM/Agda/Clay promotion."""
from fractions import Fraction as Q
from itertools import product
import json

def verify(charges, losses, eta, budget):
    charges, losses = list(map(Q, charges)), list(map(Q, losses))
    eta, budget = Q(eta), Q(budget)
    assert len(charges) == len(losses)+1 and len(charges)>=2
    assert eta > 0 and eta + budget <= charges[0]
    assert all(charges[i] <= charges[i+1]+losses[i]
               for i in range(len(losses)))
    running = Q(0)
    for i,value in enumerate(charges):
        assert running <= budget and charges[0] <= value+running
        assert value >= eta
        if i<len(losses):
            running += losses[i]
    return True

def selftest():
    eta=Q(1,64); budget=Q(1,32)
    initial=eta+budget+Q(1,128)
    losses=[Q(1,64)*Q(1,2)**n for n in range(192)]
    charges=[initial]
    for loss in losses: charges.append(charges[-1]-loss)
    assert verify(charges,losses,eta,budget)
    bad=[
      ([Q(1,16),Q(0)],[Q(1,16)],Q(1,32),Q(1,64)),
      ([Q(1,16),-Q(1,64)],[Q(1,8)],Q(1,64),Q(1,32)),
      ([Q(1,16),Q(1,64)],[Q(1,8)],Q(1,64),Q(1,8)),
      ([Q(1,16),Q(1,32)],[Q(1,32)],Q(0),Q(1,64)),
      ([Q(1,16),Q(1,64)],[-Q(1,32)],Q(1,64),Q(1,32))
    ]
    for args in bad:
        try: verify(*args)
        except AssertionError: pass
        else: raise AssertionError('invalid certificate admitted')
    accepted=0
    for a,b,c in product([Q(i,16) for i in range(4)], repeat=3):
        try:
            verify([Q(1,4),a,b,c],
                   [Q(1,4)-a,a-b,b-c],Q(1,16),Q(1,8))
        except AssertionError: pass
        else:
            accepted+=1
            assert min(a,b,c)>=Q(1,16)
    assert accepted==8
    return {'result':'PASS_EXACT_RATIONAL_REFERENCE','refinements':192,
      'eta':'1/64','budget':'1/32',
      'final_charge_ge_eta':charges[-1]>=eta,
      'negative_controls':len(bad),'exhaustive_cases':64,
      'accepted_exhaustive_cases':accepted,
      'physical_original_Wilson_certificate':False,
      'Agda_kernel_accepted':False,'Clay_endpoint':False}

if __name__=='__main__':
    print(json.dumps(selftest(), indent=2))
