#!/usr/bin/env python3
"""Exact Q(zeta_36) DFT audit on the actual 36-grid, never floating roots.

Phi_36(X)=X^12-X^6+1, with a 12-component rational coefficient
representation. Proof-by-exact-computation, not a native Agda kernel receipt.
"""
from __future__ import annotations
from fractions import Fraction as F
from dataclasses import dataclass
import json

@dataclass(frozen=True)
class Cyc:
    a:tuple
    def __post_init__(self):
        if len(self.a)!=12:raise ValueError("degree must be 12")
    def __add__(self,b):return Cyc(tuple(x+y for x,y in zip(self.a,b.a)))
    def __neg__(self):return Cyc(tuple(-x for x in self.a))
    def __sub__(self,b):return self+(-b)
    def __mul__(self,b):
        c=[F(0) for _ in range(23)]
        for i,x in enumerate(self.a):
            if x:
                for j,y in enumerate(b.a):
                    if y:c[i+j]+=x*y
        for i in range(22,11,-1):
            x=c[i]
            if x:
                c[i]=F(0);c[i-6]+=x;c[i-12]-=x
        return Cyc(tuple(c[:12]))
    def scale(self,t):return Cyc(tuple(x*t for x in self.a))
    def __pow__(self,n):
        if n<0:raise ValueError("nonnegative exponent only")
        out=ONE;base=self
        while n:
            if n&1:out=out*base
            base=base*base;n//=2
        return out

ZERO=Cyc((F(0),)*12)
ONE=Cyc((F(1),)+(F(0),)*11)
ROOT=Cyc((F(0),F(1))+(F(0),)*10)

def receipt():
    powers=[ROOT**k for k in range(36)]
    assert powers[0]==ONE and ROOT**36==ONE
    assert ROOT**12-ROOT**6+ONE==ZERO
    assert powers[18]==ONE.scale(-1)
    sums={d:sum((powers[d*j%36] for j in range(36)),ZERO)
          for d in range(36)}
    assert sums[0]==ONE.scale(36)
    assert all(sums[d]==ZERO for d in range(1,36))
    assert all(sums[(a-b)%36]==(ONE.scale(36) if a==b else ZERO)
               for a in range(36) for b in range(36))
    modes=(0,3,6,9,27,30,33)
    assert len(set(modes))==7
    coefficients={k:F(((3*k+7)%17)-8,7) for k in modes}
    samples=[sum((powers[k*j%36].scale(coefficients[k])
                  for k in modes),ZERO) for j in range(36)]
    recovered={k:sum((samples[j]*powers[(-k*j)%36]
                      for j in range(36)),ZERO).scale(F(1,36))
               for k in range(36)}
    assert all(recovered[k]==ONE.scale(coefficients.get(k,F(0)))
               for k in range(36))
    reconstructed=[sum((recovered[k]*powers[k*j%36]
                        for k in range(36)),ZERO) for j in range(36)]
    assert reconstructed==samples
    s9=lambda j:(powers[9*j%36]-powers[(-9*j)%36])
    assert all(s9(2*j)==ZERO for j in range(18))
    assert s9(1)!=ZERO
    return {
      "status":"exact_cyclotomic36_fourier_passed",
      "cyclotomic_minimal_polynomial":"x^12-x^6+1",
      "rational_vector_degree":12,
      "full_character_orthogonality_pairs":1296,
      "selected_modes":list(modes),
      "recovered_coefficients":len(modes),
      "all_36_sample_reconstruction":True,
      "float_computation":False,
      "agda_kernel_accepted":False,
      "unrestricted_continuous_sampling":False,
    }
if __name__=="__main__":print(json.dumps(receipt(),indent=2,sort_keys=True))
