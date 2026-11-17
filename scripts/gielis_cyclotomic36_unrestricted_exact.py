#!/usr/bin/env python3
"""Full arbitrary-signal C36 Fourier inversion on original Q(zeta36) scalar.

No selected-mode truncation.  Let zeta be ROOT in Q[x]/(Phi36).
F(k)=sum_j f(j)*zeta^(-kj); Inv(F)(j)=1/36 sum_k F(k)*zeta^(kj).
The exact character-resolution identity
  sum_k zeta^(k(j-l)) = 36 if j=l, else 0
plus finite distributivity proves Inv(F)=f for EVERY f in
(Q(zeta36))^36, not just a checked finite fixture.
This code enumerates all 1296 kernel entries, exercises all 36
Kronecker basis vectors and nontrivial general cyclotomic signals.

This is exact algebra with a fully specified coefficient carrier.
It is NOT kernel-accepted Agda; native C36 primitive root and
finite resolution proof remains the explicit G07/G10 leaf.
"""
from __future__ import annotations
from fractions import Fraction as F
import json
from gielis_cyclotomic36_exact import ROOT,ONE,ZERO,Cyc

N=36

def powers():
    return tuple(ROOT**k for k in range(N))

def kernel_resolution():
    p=powers()
    out={}
    for a in range(N):
        for b in range(N):
            s=sum((p[(k*(a-b))%N] for k in range(N)),ZERO)
            expectation=ONE.scale(N) if a==b else ZERO
            if s!=expectation:
                raise AssertionError(f"bad kernel ({a},{b})")
            out[(a,b)]=s
    return out

def forward(values,p=None):
    if len(values)!=N:raise ValueError("36 coefficients required")
    if p is None:p=powers()
    return tuple(
        sum((values[j]*p[(-k*j)%N] for j in range(N)),ZERO)
        for k in range(N)
    )

def inverse(coefficients,p=None):
    if len(coefficients)!=N:raise ValueError("36 coefficients required")
    if p is None:p=powers()
    return tuple(
        sum((coefficients[k]*p[(k*j)%N] for k in range(N)),ZERO).scale(F(1,N))
        for j in range(N)
    )

def basis(index):
    return tuple(ONE if j==index else ZERO for j in range(N))

def receipt():
    p=powers()
    assert ROOT**N==ONE and ROOT**18==-ONE
    assert ROOT**12-ROOT**6+ONE==ZERO
    assert len(kernel_resolution())==N*N
    for index in range(N):
        v=basis(index)
        assert inverse(forward(v,p),p)==v
        assert forward(inverse(v,p),p)==v
    # The basis equations + linearity prove the identities for EVERY
    # vector over the full original cyclotomic coefficient field.
    # The following independent non-basis vectors detect plumbing
    # mistakes and guarantee non-real scalar coordinates were tested.
    arbitrary=[]
    arbitrary.append(tuple(ONE.scale(F(2*i-31,7)) for i in range(N)))
    arbitrary.append(tuple(p[(11*i)%N].scale(F((i%7)+1,11))
                           for i in range(N)))
    arbitrary.append(tuple(sum((p[(k*i)%N].scale(F(k+1,17))
                        for k in (1,5,7,11,13)),ZERO) for i in range(N)))
    for v in arbitrary:
        assert inverse(forward(v,p),p)==v
        assert forward(inverse(v,p),p)==v
    return {
      "status":"full_arbitrary_36_signal_C36_inversion_exact",
      "original_scalar":"Q[zeta36]=Q[x]/(x^12-x^6+1)",
      "coefficient_rational_dimension":12,
      "full_character_resolution_entries":1296,
      "forward_inverse_basis_vectors":36,
      "inverse_forward_basis_vectors":36,
      "general_nonbasis_cyclotomic_vectors":len(arbitrary),
      "universal_arbitrary_signal_by_linearity_and_basis":True,
      "no_selected_mode_restriction":True,
      "no_float_in_field_or_transform":True,
      "native_Agda_C36_instantiation_accepted":False,
    }

if __name__=="__main__":
    print(json.dumps(receipt(),indent=2,sort_keys=True))
