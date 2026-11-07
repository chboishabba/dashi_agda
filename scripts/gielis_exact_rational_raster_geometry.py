#!/usr/bin/env python3
"""EXACT rational Gielis domain raster mask, for every positive integer mode.

Selected analytic Gielis formula:
   r_m(theta) = 2/sqrt(3+cos(m*theta)).

For rational x,y and q=x*x+y*y>0, write z=x+iy.
Then cos(m theta) = Re(z**m)/q**(m/2).
The EXACT radial inside test is

    (3*q-4)*q**(m/2) + q*Re(z**m) < 0.

For even m, all terms are rational.
For odd m, define A=(3q-4)*q**((m-1)//2), B=q*Re(z**m).
The predicate A*sqrt(q)+B<0 is decided without computing sqrt:
  A=0: B<0;
  A>0: B<0 and A*A*q < B*B;
  A<0: B<=0 or A*A*q > B*B.

The q=0 origin is inside. All comparisons use Fraction integer
arithmetic, so no fixed binary64 boundary-classification error
survives as mesh size decreases.

This classifies the *exact unshrunken domain*. Original n41/n61
legacy 1e-12 masks were independently verified identical for the
selected modes; for general n it is the original mathematical
domain rather than a floating epsilon-shrunken approximation.
"""
from __future__ import annotations
from fractions import Fraction as F
from functools import lru_cache
import argparse
import json
import numpy as np

def complex_integer_power_real(x:F,y:F,m:int)->F:
    if type(m) is not int or m<0:raise ValueError("nonnegative integral exponent")
    re,im=F(1),F(0)
    ar,ai=x,y
    while m:
        if m&1:
            re,im=re*ar-im*ai,re*ai+im*ar
        ar,ai=ar*ar-ai*ai,2*ar*ai
        m//=2
    return re

def exact_inside_gielis(x:F,y:F,m:int)->bool:
    if type(m) is not int or m<=0:raise ValueError("positive integer m")
    x,y=F(x),F(y)
    q=x*x+y*y
    if q==0:return True
    real=complex_integer_power_real(x,y,m)
    B=q*real
    A=(3*q-4)*q**(m//2)
    if m%2==0:
        return A+B<0
    if A==0:return B<0
    if A>0:return B<0 and A*A*q<B*B
    return B<=0 or A*A*q>B*B

def grid_coordinate(n:int,i:int)->F:
    if type(n) is not int or n<3 or type(i) is not int or i<0 or i>=n:
        raise ValueError("grid index outside valid range")
    return F(3*(2*i-(n-1)),2*(n-1))

@lru_cache(maxsize=16)
def _mask_flat(n:int,m:int):
    if type(n) is not int or n<17 or n%2!=1:
        raise ValueError("odd grid n>=17 required")
    if type(m) is not int or m<=0:
        raise ValueError("positive integer m required")
    coords=[grid_coordinate(n,i) for i in range(n)]
    return tuple(exact_inside_gielis(x,y,m) for x in coords for y in coords)

def exact_mask(m:int,n:int):
    return np.array(_mask_flat(n,m),dtype=bool).reshape(n,n)

def receipt(m=3,n=41):
    import gielis_base369_experiments as G
    result=exact_mask(m,n)
    grid=np.linspace(-1.5,1.5,n)
    x,y=np.meshgrid(grid,grid,indexing="ij")
    old=np.hypot(x,y)<G.gielis_radius(np.arctan2(y,x),m)-1e-12
    return {
        "status":"exact_unshrunken_Gielis_raster_classification",
        "mode":m,"n":n,
        "integer_fraction_only_for_membership":True,
        "analytic_gielis_radius":"2/sqrt(3+cos(m*theta))",
        "squared_comparison_preserves_strictness":True,
        "interior_nodes":int(result.sum()),
        "legacy_float_mask_disagreements":int((old!=result).sum()),
        "fixed_binary64_boundary_error_in_membership":False,
        "matched_exact_unshrunken_domain":True,
        "Agda_native_rational_predicate_kernel_accepted":False,
        "quantitative_FD_eigenvalue_continuum_error_proved":False,
    }

if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--m",type=int,default=3)
    p.add_argument("--grid",type=int,default=41)
    a=p.parse_args()
    print(json.dumps(receipt(a.m,a.grid),indent=2,sort_keys=True))
