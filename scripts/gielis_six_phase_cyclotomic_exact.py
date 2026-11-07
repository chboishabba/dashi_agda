#!/usr/bin/env python3
"""Exact six-phase C2×C3 Fourier interoperability with Q(zeta36).

Uses literal CRT indices:
  j even: [0,4,2] -> residues (0,1,2) mod3
  j odd:  [3,1,5] -> residues (0,1,2) mod3.
The source C3 DFT owner uses (ω²,ω) for mode 1/2,
consistent with the negative-exponent forward six-point DFT.
The mode mapping is k=(3r+2s) mod6.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import product
import json
from gielis_cyclotomic36_exact import ROOT, ONE, ZERO

OMEGA=ROOT**12
OMEGA2=ROOT**24
NEG=ONE.scale(-1)

def plus(a,b):return a+b
def minus(a,b):return a-b
def f3(v):
    a,b,c=v
    return (a+b+c,a+OMEGA2*b+OMEGA*c,a+OMEGA*b+OMEGA2*c)
def i3(v):
    a,b,c=v
    return ((a+b+c).scale(Q(1,3)),
            (a+OMEGA*b+OMEGA2*c).scale(Q(1,3)),
            (a+OMEGA2*b+OMEGA*c).scale(Q(1,3)))

def crt_values(v):
    return ((v[0],v[4],v[2]),(v[3],v[1],v[5]))

def from_crt(values):
    a,b=values
    return (a[0],b[1],a[2],b[0],a[1],b[2])

def f6(v):
    even,odd=crt_values(v)
    return (f3(tuple(a+b for a,b in zip(even,odd))),
            f3(tuple(a-b for a,b in zip(even,odd))))

def i6(t):
    e,o=(i3(t[0]),i3(t[1]))
    ev=tuple((a+b).scale(Q(1,2)) for a,b in zip(e,o))
    od=tuple((a-b).scale(Q(1,2)) for a,b in zip(e,o))
    return from_crt((ev,od))

def direct6(v):
    return tuple(sum((v[j]*(ROOT**((-6*k*j)%36))
                      for j in range(6)),ZERO)
                 for k in range(6))

def receipt():
    assert OMEGA**3==ONE and OMEGA+OMEGA2+ONE==ZERO
    modes=(0,2,4,3,5,1)
    count=0
    for ints in product((-1,0,1),repeat=6):
        v=tuple(ONE.scale(Q(i)) for i in ints)
        t=f6(v)
        assert i6(t)==v
        assert f6(i6(t))==t
        brute=direct6(v)
        selected=tuple(t[r][s] for r in range(2) for s in range(3))
        assert selected==tuple(brute[k] for k in modes)
        count+=1
    return {
      "status":"exact_C6_CRT_cyclotomic_Fourier_reuse_passed",
      "source":"original C3CubeCyclotomicFourierExact and Q(zeta36)",
      "site_index_even":[0,4,2],
      "site_index_odd":[3,1,5],
      "mode_indices":[0,2,4,3,5,1],
      "sample_vectors_exact":count,
      "componentwise_full_C6_roundtrip":True,
      "crosscheck_with_direct_Q_zeta36_DFT":True,
      "C6_C2xC3_CRT_correct":True,
      "full_C36_DFT_accepted":False,
      "agda_kernel_accepted":False,
    }
if __name__=="__main__":
    print(json.dumps(receipt(),indent=2,sort_keys=True))
