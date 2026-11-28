#!/usr/bin/env python3
"""BR42: original physical Israel-work to variable BR4 energy/restart ledger.

Exact Fraction arithmetic; NO NumPy/OpenBLAS, no PDE solver.
The analytic trace estimate, metric evolution and zero-mode controls are
explicit INPUT CERTIFICATES; the script never invents them.

The source consumes the actual BR35 frequency-loss budget (M=12Q),
BR41 real Israel work inequality, BR4 variable symmetric energy and
BR40b-f differentiated physical D/E force and signed graph residual.

This is an acceptance harness / candidate constructor, not a theorem
of Einstein-Israel well-posedness or a proof of a physical trace estimate.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from typing import Tuple
import argparse, json
from pathlib import Path

def R(x): return F(x)
def ceildiv(a,b): return -(-a//b)

@dataclass(frozen=True)
class PhysicalLoss:
    chart_quality: F
    metric_power: int = 4
    subsidiary_power: int = 2
    def __post_init__(self):
        if self.chart_quality<1: raise ValueError('chart quality Q must be >=1')
        if (self.metric_power,self.subsidiary_power)!=(4,2):
            raise ValueError('retain the actual BR37 exponents')
    @property
    def M(self): return 12*self.chart_quality
    @property
    def metric(self): return self.M**self.metric_power
    @property
    def subsidiary(self): return self.M**self.subsidiary_power
    @property
    def derivative_loss(self):
        # Polynomial growth order as Q -> infinity, NOT a proved variable PDE
        # Sobolev estimate. There is no uniform constant independent of Q.
        return self.metric_power,self.subsidiary_power

@dataclass(frozen=True)
class WallPayload:
    """Squared positive real trace source (all original channels retained)."""
    israel_sq: F
    q_sq: F
    shift_jump_sq: F
    j_sq: F
    scale_sum_sq: F
    def __post_init__(self):
        if min(self.israel_sq,self.q_sq,self.shift_jump_sq,
               self.j_sq,self.scale_sum_sq)<0:
            raise ValueError('negative squared physical channel')
    def expanded(self):
        return 3*(self.israel_sq+
                  4*self.q_sq*self.shift_jump_sq+
                  4*self.j_sq*self.scale_sum_sq)

@dataclass(frozen=True)
class TraceEstimate:
    """USER/ANALYTIC PROOF OBLIGATION:
    wall_velocity_sq <= c_energy*bulk_energy + c_data*data_sq.
    Every estimate is scoped to one physical variable chart and one
    derivative level. These numerical coefficients alone are not witnesses.
    """
    c_energy: F
    c_data: F
    def __post_init__(self):
        if min(self.c_energy,self.c_data)<0:raise ValueError('negative trace coefficient')

@dataclass(frozen=True)
class Slab:
    """BR4 real physical energy balance after exact signed wall split."""
    duration: F
    bulk_growth: F
    trace: TraceEstimate
    epsilon: F
    def __post_init__(self):
        if self.duration<=0 or self.bulk_growth<0 or self.epsilon<=0:
            raise ValueError('invalid damped real-time slab')
    def coefficients(self):
        # From BR41: 2 eps |W| <= eps² V² + P
        # => 2|W| <= eps V² + P/eps.
        # BR4 energy ineq: E_next <= (1+h*a) E + h*(source_sq+2|W|).
        # Supply trace inequality for V². Keep its data source separate.
        a=self.bulk_growth+self.epsilon*self.trace.c_energy
        wall_data=self.epsilon*self.trace.c_data
        return 1+self.duration*a, self.duration*(1+wall_data), self.duration/self.epsilon
    def step(self,energy,bulk_data_sq,payload):
        energy=R(energy); bulk_data_sq=R(bulk_data_sq)
        if min(energy,bulk_data_sq)<0:raise ValueError('negative physical energy/data')
        m,d,p=self.coefficients()
        return m*energy+d*bulk_data_sq+p*payload.expanded()
    def zero_mode_step(self,mode,mode_forcing):
        # Mode coefficient is transported, NOT projected away. This
        # discrete ledger represents the supplied normal holonomy moment.
        return R(mode)+self.duration*R(mode_forcing)

@dataclass(frozen=True)
class RestartGuard:
    """Conditions checked BEFORE an accepted physical slab can restart.
    All witnesses must be supplied from actual fields/geometry; no pass
    is generated just because the arithmetic bounds are finite.
    """
    min_lapse: F
    min_normal_jacobian: F
    min_boundary_spacelike_gap: F
    exterior_weight_margin: F
    chart_compatible: bool
    physical_constraint_paid: bool
    source_matched: bool
    trace_inequality_paid: bool
    curvature_quotient_paid: bool
    def allowed(self):
        return (min(self.min_lapse,self.min_normal_jacobian,
                    self.min_boundary_spacelike_gap,
                    self.exterior_weight_margin)>0
                and self.chart_compatible and self.physical_constraint_paid
                and self.source_matched and self.trace_inequality_paid
                and self.curvature_quotient_paid)

def scenario():
    return (Slab(F(1,20),F(3,7),TraceEstimate(F(5,3),F(2,9)),
                 F(1,4)),
            WallPayload(F(3,8),F(4,9),F(1,5),F(36,25),F(7,11)))

def run():
    slab,payload=scenario()
    loss=PhysicalLoss(F(7,3))
    assert loss.M==28 and loss.metric==28**4 and loss.subsidiary==28**2
    m,d,p=slab.coefficients()
    assert m==1+slab.duration*(slab.bulk_growth+slab.epsilon*slab.trace.c_energy)
    assert d==slab.duration*(1+slab.epsilon*slab.trace.c_data)
    assert p==slab.duration/slab.epsilon
    e=F(3,2); mode=F(-5,7)
    cursor=[]
    for n in range(16):
        bulk=F(n+2,17); source=payload if n%3 else WallPayload(F(0),F(0),F(0),F(0),F(0))
        next_e=slab.step(e,bulk,source)
        assert next_e>=0
        mode_next=slab.zero_mode_step(mode,F((n%5)-2,13))
        # Identity of the exact signed recurrence and its frozen coefficient.
        assert next_e==m*e+d*bulk+p*source.expanded()
        cursor.append([n,str(e),str(next_e),str(mode),str(mode_next)])
        e,mode=next_e,mode_next
    # Rigorous discrete Duhamel/Gronwall expression via exact F.
    energies=[F(3,2)]
    inputs=[]
    for n in range(16):
        bulk=F(n+2,17); source=payload if n%3 else WallPayload(F(0),F(0),F(0),F(0),F(0))
        inputs.append(d*bulk+p*source.expanded())
        energies.append(slab.step(energies[-1],bulk,source))
    closed=m**16*energies[0]+sum(m**(15-k)*u for k,u in enumerate(inputs))
    assert energies[-1]==closed==e
    # Negative control: without actual PDE witnesses, no physical promotion.
    guard=RestartGuard(F(1),F(1),F(1),F(1),True,False,True,False,False)
    assert not guard.allowed()
    guard2=RestartGuard(F(1),F(1),F(1),F(1),True,True,True,True,True)
    assert guard2.allowed() # formal boolean only; no automatic proof source
    assert not RestartGuard(F(1),F(0),F(1),F(1),True,True,True,True,True).allowed()
    # Strict growth under Q: no uniform Kreiss or hidden glancing bound.
    lower=PhysicalLoss(F(1)); higher=PhysicalLoss(F(9))
    assert higher.metric>lower.metric and higher.subsidiary>lower.subsidiary
    print(json.dumps(dict(scope='exact physical source energy arithmetic, not PDE existence',
      steps=len(cursor),metric_loss=loss.metric,subsidiary_loss=loss.subsidiary,
      source_power=str(payload.expanded()),last_bound=str(e),zero_mode=str(mode),
      duhamel='PASS',physical_promotion='BLOCKED absent actual certificate',
      guards='PASS',checks='PASS'),sort_keys=True))

if __name__=='__main__':run()
