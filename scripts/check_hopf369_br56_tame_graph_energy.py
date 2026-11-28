#!/usr/bin/env python3
"""BR56: exact derivative-paid moving Israel graph energy cut, order <=8.

Uses actual BR52 divided ADM graph coefficients and BR54 mixed wall
Leibniz. The source-level product inequality for any |alpha|<=s is
 ||D^alpha(k·du)||_w <= Σ_{beta<=alpha} C(alpha,beta)
       ||D^beta k||_infty ||D^(alpha-beta)du||_w.
If every such norm is controlled by K_s and U_s, then a sufficient
per-index bound is 2^s K_s U_s (four wall coordinates). The original
density D contributes its own product jets and does not disappear.

For the true signed wall source:
  2|<V,W_graph>| <= eps ||V||² +
                        eps^-1 (Dmax*2^s*K_s*U_s)².
The BR43 two-sided trace theorem pays ||V||² ONLY with E and the
higher-energy D_h. This script computes exact conditional rates for
BR44, retains BR37 Q^4 / Q² losses and rejects missing estimates.
It does NOT construct the non-linear Einstein solution, positivity
witnesses or a uniform Kreiss bound.

Independent algebra: --part coeff|energy|refusal.
"""
from fractions import Fraction as F
from math import comb
from dataclasses import dataclass
import argparse

def R(x):return F(x)

@dataclass(frozen=True)
class HighOrderGraph:
    order:int
    density_max:F
    coefficient_Winf:F
    field_Hs:F
    def __post_init__(self):
        if not 0<=self.order<=8:raise ValueError("BR4 order limit")
        if min(self.density_max,self.coefficient_Winf,self.field_Hs)<0:
            raise ValueError("negative norm bound")
    @property
    def coefficient(self):
        return self.density_max*(2**self.order)*self.coefficient_Winf
    @property
    def source_norm(self):
        return self.coefficient*self.field_Hs

@dataclass(frozen=True)
class RealTraceOwner:
    lower_to_wall:F
    higher_to_wall:F
    higher_field_control:F
    physical_trace_proved:bool=False
    physical_graph_coefficient_proved:bool=False
    def __post_init__(self):
        if min(self.lower_to_wall,self.higher_to_wall,self.higher_field_control)<0:
            raise ValueError("negative norm comparison")
    def paid(self):return self.physical_trace_proved and self.physical_graph_coefficient_proved

@dataclass(frozen=True)
class GraphEnergyWeld:
    graph:HighOrderGraph
    trace:RealTraceOwner
    epsilon:F
    def __post_init__(self):
        if self.epsilon<=0:raise ValueError("positive Young epsilon required")
    def conditional_rates(self):
        # Work coefficient multiplies the actual SOURCE higher
        # derivative norm, NOT an invented lower-order bound.
        G=self.graph.coefficient
        return (self.epsilon*self.trace.lower_to_wall,
                self.epsilon*self.trace.higher_to_wall
                +G*G*self.trace.higher_field_control/self.epsilon)
    def admit(self):
        if not self.trace.paid():raise ValueError("missing physical tame/trace proof witness")
        return self.conditional_rates()

def coeff():
    from check_hopf369_br52_all_order_material_flux import (
        make_source,field_jet,canonical_graph_error,coeff as deriv_coeff,
        dot,mul,add,const,ORDER,
    )
    src=make_source()
    for dim in (15,5):
        for ch in range(dim):
            jet=[field_jet(ch,0,i) for i in range(5)]
            err,_=canonical_graph_error(src,jet)
            N,H,v,Hi,D,Ninv2,Fspace,Ftime,theta,kt,ks=src
            allk=[mul(D,kt)]+[mul(D,k) for k in ks]
            for n in range(ORDER+1):
                upper=sum((F(comb(n,a))*abs(deriv_coeff(allk[mu],a))*
                           abs(deriv_coeff(jet[mu],n-a))
                           for a in range(n+1) for mu in range(5)),F(0))
                assert abs(deriv_coeff(err,n))<=upper
    print("PASS BR56 original 15/5 ADM conormal derivative majorants, all 9 Taylor orders")

def energy():
    from check_hopf369_br44_two_level_energy import PhysicalCoupledRates
    from check_hopf369_br42_physical_energy_restart import PhysicalLoss
    e=F(1,3)
    lower=F(5,7);higher=F(9,11)
    for order in range(9):
        g=HighOrderGraph(order,F(6,5),F(1,13),F(3,7))
        r=RealTraceOwner(lower,higher,F(4,5),True,True)
        low,high=GraphEnergyWeld(g,r,e).admit()
        assert low==e*lower
        assert high>=e*higher
        rates=PhysicalCoupledRates(F(2,5)+low,F(3,7)+high,F(5,11),F(7,13))
        assert rates.common_rate(F(4,3))>0
        assert g.coefficient==F(6,5)*2**order/F(13)
    los=PhysicalLoss(F(7,3))
    assert los.derivative_loss==(4,2)
    print("PASS BR56 9 exact order-graded high/low energy source budgets, original BR37 polynomial loss")

def refusal():
    g=HighOrderGraph(8,F(5,4),F(1,9),F(2,7))
    r=RealTraceOwner(F(3,5),F(4,7),F(8,9),False,False)
    try:GraphEnergyWeld(g,r,F(1,5)).admit()
    except ValueError:pass
    else:raise AssertionError("unpaid physical source was promoted")
    assert HighOrderGraph(8,F(1),F(1),F(1)).coefficient==256
    print("PASS BR56 fail closed: absent true BR4 trace/tame proofs and 256-order worst-case")

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--part',choices=['coeff','energy','refusal'],default='energy')
    x=p.parse_args()
    {'coeff':coeff,'energy':energy,'refusal':refusal}[x.part]()

if __name__=='__main__':main()
