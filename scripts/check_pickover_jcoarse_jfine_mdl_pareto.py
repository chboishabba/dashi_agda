#!/usr/bin/env python3
"""Pickover consumer-adequate Pareto front, operational description vs cost.
Illustrative finite rational phase fixtures; no assertion for 99^(9999!).
Donors: DASHI Core AdmissibleConsumerMDLHyperfabricExact,
RecursiveParetoFrontierLiftingExact, Biology JCoarseFineConsumerReductionBridgeExact.
"""
from dataclasses import dataclass
from fractions import Fraction

@dataclass(frozen=True)
class Candidate:
    name:str
    description_bits:int
    producer_steps:int
    checker_steps:int
    residual_bits:int
    adequate:bool

def front(cs):
    eligible=[x for x in cs if x.adequate]
    axes=lambda x:(x.description_bits,x.producer_steps,x.checker_steps,x.residual_bits)
    return [x for x in eligible if not any(y!=x and all(a<=b for a,b in zip(axes(y),axes(x))) and any(a<b for a,b in zip(axes(y),axes(x))) for y in eligible)]

def sign(x):
    x=x%1
    return 0 if x in (0,Fraction(1,2)) else 1 if x<Fraction(1,2) else -1

def main():
    phases=(Fraction(5,12),Fraction(7,12))
    sector=lambda x:int(3*(x%1))
    assert sector(phases[0])==sector(phases[1])==1
    assert sign(phases[0])!=sign(phases[1])
    models=[
        Candidate('C3 sector only',2,1,1,0,False),
        Candidate('full rational retained phase',100,100,20,80,True),
        Candidate('signed query witness',12,40,10,1,True),
        Candidate('recharted coarse sector',5,2,2,0,False),
        Candidate('wasteful full-state copy',120,150,40,90,True),
    ]
    f=front(models)
    assert {x.name for x in f}=={'full rational retained phase','signed query witness'} or {x.name for x in f}=={'signed query witness'}
    assert all(x.adequate for x in f)
    print('PASS: inadmissible coarse-only observer excluded even when tiny')
    print('PARETO:',[(x.name,x.description_bits,x.producer_steps,x.checker_steps,x.residual_bits) for x in f])
    print('COST VALUES: illustrative fixtures, not empirical runtime or Kolmogorov lower bounds')
    print('OPEN: construct actual pi-phase certificate and verified cost bounds')
if __name__=='__main__':main()
