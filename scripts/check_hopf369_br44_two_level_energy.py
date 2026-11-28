#!/usr/bin/env python3
"""BR44 two-level physical energy small-gain/derivative closure.

Actual analytic input is a differentiated BR4 upper energy inequality:
E'<=a E+b D+f, D'<=c E+d D+g, E,D>=0.
BR43 provides b=eps*(2L c_n/m), a includes eps*(4c_v/(Lm)).
This DOES NOT prove the differentiated BR4 estimate, nonlinear PDE
existence, uniform stability or admissible initial corner data.

For lambda>0, H=E+lambda D:
H'<=max(a+lambda*c, d+b/lambda)*H +f+lambda*g.
All arithmetic is exact rationals and positivity of inputs is checked.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from check_hopf369_br42_physical_energy_restart import WallPayload

@dataclass(frozen=True)
class PhysicalCoupledRates:
    low_growth: F
    low_from_high: F
    high_from_low: F
    high_growth: F
    def __post_init__(self):
        if min(self.low_growth,self.low_from_high,
               self.high_from_low,self.high_growth)<0:
            raise ValueError("growth majorants must be nonnegative")
    def common_rate(self,lam):
        lam=F(lam)
        if lam<=0:raise ValueError("positive high-energy weighting required")
        return max(self.low_growth+lam*self.high_from_low,
                   self.high_growth+self.low_from_high/lam)
    def residuals(self,lam):
        c=self.common_rate(lam)
        return c-self.low_growth-lam*self.high_from_low,               lam*c-self.low_from_high-lam*self.high_growth

@dataclass(frozen=True)
class PhysicalHigherSlab:
    h: F
    lam: F
    rates: PhysicalCoupledRates
    def __post_init__(self):
        if min(self.h,self.lam)<=0:raise ValueError("positive h,lambda")
    def budget(self,E,D,f,g):
        if min(E,D,f,g)<0:raise ValueError("negative signed physical norm majorant")
        rate=self.rates.common_rate(self.lam)
        H=E+self.lam*D
        return (1+self.h*rate)*H+self.h*(f+self.lam*g)
    def compare(self,E,D,f,g):
        a,b,c,d=(self.rates.low_growth,self.rates.low_from_high,
                 self.rates.high_from_low,self.rates.high_growth)
        En=E+self.h*(a*E+b*D+f)
        Dn=D+self.h*(c*E+d*D+g)
        assert En+self.lam*Dn<=self.budget(E,D,f,g)
        return En,Dn

def run():
    # BR43 physical reference requires 1<L=2log2<2 and m=b²>=16/25.
    # Conservative rational bound retains separate lower/upper L.
    m=F(16,25);eps=F(1,4)
    cv=F(3,2);cn=F(5,3)
    a=F(3,7)+eps*4*cv/(F(1)*m)
    b=eps*2*F(2)*cn/m
    # c,d are INDEPENDENT high-order PDE estimate INPUTS, not fabricated
    # constants established for Einstein-Israel by the rational example.
    rates=PhysicalCoupledRates(a,b,F(2,7),F(5,9))
    lam=F(3,2);step=PhysicalHigherSlab(F(1,20),lam,rates)
    r0,r1=rates.residuals(lam)
    assert r0>=0 and r1>=0
    E,D=F(2,3),F(7,5)
    f,g=F(3,11),F(5,13)
    weighted_initial=E+lam*D
    for k in range(16):
        e0,d0=E,D
        E,D=step.compare(E,D,f+F(k,71),g+F(k,91))
        bound=step.budget(e0,d0,f+F(k,71),g+F(k,91))
        assert E+lam*D<=bound
        assert E>=e0 and D>=d0
    # Nonzero normal-velocity higher energy increases the source K:
    assert rates.common_rate(F(1))>=rates.low_growth
    assert rates.common_rate(F(1))>=rates.high_growth
    # If no high-order estimate is supplied, it is not valid to insert
    # c=d=0. The required physical PDE witness is external to this script.
    print("PASS BR44 exact two-level Duhamel majorant, 16 source-paid slabs")
    print("PASS residual nonnegativity and preserved differentiated-energy premium")
    print("CONDITIONAL: must prove BR4 differentiated high-energy rates and physical boundary estimate")

if __name__=="__main__":run()
