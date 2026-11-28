#!/usr/bin/env python3
"""BR43b physical trace payment into the original BR42 restart, fail-closed.

The trace theorem itself is unconditional for H^1 normal fields. The physical
energy closure requires an independently constructed higher BR4 energy which
controls the normal derivative of the boundary velocity. We preserve it as
a separate input D rather than quietly using E for both.

No Hilbert-space proof is inferred from finite rational examples.
"""
from fractions import Fraction as F
from dataclasses import dataclass
from check_hopf369_br42_physical_energy_restart import WallPayload,PhysicalLoss

@dataclass(frozen=True)
class NormalTraceBound:
    normal_length_lower: F
    weight_lower: F
    velocity_mass_to_energy: F
    derivative_mass_to_higher_energy: F
    def __post_init__(self):
        if min(self.normal_length_lower,self.weight_lower,
               self.velocity_mass_to_energy,
               self.derivative_mass_to_higher_energy)<=0:
            raise ValueError("positive domain/weight and coercive energy comparison required")
    @property
    def cE(self):
        return 4*self.velocity_mass_to_energy/(self.normal_length_lower*self.weight_lower)
    @property
    def cD(self):
        return 2*self.normal_length_lower*self.derivative_mass_to_higher_energy/self.weight_lower
    def normal_trace_upper(self,low_energy,high_energy):
        if min(low_energy,high_energy)<0:raise ValueError("energies must be positive")
        return self.cE*low_energy+self.cD*high_energy

@dataclass(frozen=True)
class SourcePaidRestart:
    """Only the inequality (conditional on actual BR4 energy comparisons).
    No guessed positive new symmetrizer or automatic PDE solvability.
    """
    h: F
    a: F
    epsilon: F
    trace: NormalTraceBound
    def __post_init__(self):
        if self.h<=0 or self.a<0 or self.epsilon<=0:raise ValueError("invalid slab")
    def rhs(self,initial,high_energy,bulk_sq,payload):
        if min(initial,high_energy,bulk_sq)<0:raise ValueError("invalid input energies")
        return ((1+self.h*(self.a+self.epsilon*self.trace.cE))*initial
               +self.h*self.epsilon*self.trace.cD*high_energy
               +self.h*bulk_sq+self.h/ self.epsilon*payload.expanded())
    def absorb(self,low_energy,high_energy,bulk_sq,payload,actual_wall_sq):
        # Actual wall estimate source must be supplied independently.
        if actual_wall_sq>self.trace.normal_trace_upper(low_energy,high_energy):
            raise ValueError("physical trace estimate not paid")
        return ((1+self.h*self.a)*low_energy
                +self.h*bulk_sq+self.h*
                (self.epsilon*actual_wall_sq+payload.expanded()/self.epsilon))

def run():
    # Physical BS11/BR31 original warp: L=2log2, w_min=(4/5)^p.
    # The exact theorem's coefficients retain log2. For this bounded
    # rational arithmetic audit take L_lower=1 (since 2log2>1) AND
    # L_upper=2 (since 2log2<2). 1/L uses the lower bound; L the upper.
    # They are separate and cannot be conflated.
    m=F(16,25)
    mass_to_E=F(3,2);derivative_to_D=F(5,3)
    cE=4*mass_to_E/(F(1)*m)
    cD=2*F(2)*derivative_to_D/m
    class Conservative:
        def __init__(self):
            self.cE=cE;self.cD=cD
        def normal_trace_upper(self,E,D):return cE*E+cD*D
    trace=Conservative()
    pay=SourcePaidRestart(F(1,20),F(3,7),F(1,4),trace)
    P=WallPayload(F(2,9),F(3,8),F(4,7),F(36,25),F(1,5))
    E=F(7,6);D=F(11,9);Fbulk=F(13,17)
    V=trace.normal_trace_upper(E,D)
    actual=pay.absorb(E,D,Fbulk,P,V)
    upper=pay.rhs(E,D,Fbulk,P)
    assert actual==upper
    assert trace.cD>0
    # Make the extra derivative indispensable: no automatic absorption
    # into lower E even for identical physical inputs.
    assert pay.rhs(E,D+1,Fbulk,P)>upper
    assert pay.rhs(E,D,Fbulk,P)==upper
    # Bad normal trace witnesses are rejected rather than considered zero.
    try:
        pay.absorb(E,D,Fbulk,P,V+1)
        assert False,"missing trace witness accepted"
    except ValueError:
        pass
    loss=PhysicalLoss(F(5,2))
    assert loss.derivative_loss==(4,2)
    print("PASS exact derivative-charged two-ended physical energy recurrence")
    print("PASS strict unpaid trace rejection and BR37 polynomial loss retention")
    print("CONDITIONAL: higher BR4 energy must control partial_n partial_t H; no PDE theorem accepted")

if __name__=="__main__":run()
