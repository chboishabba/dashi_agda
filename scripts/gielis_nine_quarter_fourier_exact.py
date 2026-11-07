#!/usr/bin/env python3
"""Reconcile native rational m9 quarter-wave Fourier with actual Q(zeta36).

This is the exact selected four-phase real character subspace:
  1, cos(9*2πj/36), sin(9*2πj/36), cos(18*2πj/36).
Unlike an unrestricted C36 theorem, all four character rows take values
in rational {-1,0,1}. The other C36 modes still need cyclotomic scalars.
"""
from __future__ import annotations
from fractions import Fraction as Q
import json
from itertools import product
from gielis_cyclotomic36_exact import ROOT, ONE, ZERO

def forward(v):
    a,b,c,d=map(Q,v)
    return (
        (a+b+c+d)/4,
        (a-c)/2,
        (b-d)/2,
        (a-b+c-d)/4,
    )

def inverse(t):
    a,b,c,d=map(Q,t)
    return (a+b+d,a+c-d,a-b+d,a-c-d)

def receipt():
    z=[ROOT**(9*j) for j in range(4)]
    zi=[ROOT**((36-9*j)%36) for j in range(4)]
    imaginary=ROOT**9
    assert imaginary*imaginary==-ONE
    inv_imaginary=-imaginary
    real_cos=[(a+b).scale(Q(1,2)) for a,b in zip(z,zi)]
    real_sin=[((a-b)*inv_imaginary).scale(Q(1,2))
              for a,b in zip(z,zi)]
    cos18=[ROOT**((18*j)%36) for j in range(4)]
    zeroes=[ZERO,ONE,-ONE]
    assert all(x in zeroes for x in real_cos+real_sin+cos18)
    cos_expected=[ONE,ZERO,-ONE,ZERO]
    sin_expected=[ZERO,ONE,ZERO,-ONE]
    cos18_expected=[ONE,-ONE,ONE,-ONE]
    assert real_cos==cos_expected and real_sin==sin_expected
    assert cos18==cos18_expected
    assert forward((Q(1),Q(0),Q(-1),Q(0))) == (0,1,0,0)
    assert forward((Q(0),Q(1),Q(0),Q(-1))) == (0,0,1,0)
    assert forward((Q(1),Q(-1),Q(1),Q(-1))) == (0,0,0,1)
    checks=0
    for v in product(range(-2,3),repeat=4):
        t=forward(v)
        assert inverse(t)==tuple(map(Q,v))
        assert forward(inverse(t))==t
        checks+=1
    return {
      "status":"exact_quarter_wave_fourier_passed",
      "selected_carrier":"existing Gielis Phase36 j=0..3",
      "original_cyclotomic_field":"Q[zeta36]=Q[x]/(x^12-x^6+1)",
      "selected_basis":["constant","cosine9","sine9","cosine18"],
      "basis_values":[[1,1,1,1],[1,0,-1,0],[0,1,0,-1],[1,-1,1,-1]],
      "exact_rational_roundtrips":checks,
      "same_original_zeta36_characters":True,
      "real_frequency_9_separates_coarse_Nyquist_alias":True,
      "full_C36_native_fourier_accepted":False,
      "agda_kernel_accepted":False,
    }
if __name__=="__main__":
    print(json.dumps(receipt(),indent=2,sort_keys=True))
