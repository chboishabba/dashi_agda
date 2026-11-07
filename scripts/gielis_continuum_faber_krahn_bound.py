#!/usr/bin/env python3
"""Rigorous rational first continuum Dirichlet eigenvalue lower bound.

For selected special Gielis domains all integer m share exact area
|Omega_m| = sqrt(2)*pi. Faber-Krahn gives
 lambda1(Omega_m) >= j_{0,1}^2 / sqrt(2),
where j_{0,1} is the first positive zero of Bessel J0.

Prove j_{0,1}>12/5 using only exact rational series:
  J0(x)=sum_{k>=0}(-1)^k(x²/4)^k/(k!)².
At x=12/5, terms decrease after k=1. The odd k=5
partial sum S5 is a STRICT positive lower bound.

For 0<x<=12/5, J1(x)=(x/2)*sum_{k>=0}
 (-1)^k(x²/4)^k/[k!(k+1)!].
The inner alternating sequence decreases from k=0 since
(x²/4)/[(k+1)(k+2)] <= 18/25 <1.
Its sum is >= 1-x²/8 >= 7/25 >0.
Because J0'=-J1, J0 is strictly decreasing on
(0,12/5) and J0(12/5)>0, so its first zero >12/5.

Since sqrt(2)<99/70 (verified by rational squares),
  lambda1(Omega_m)> (12/5)^2*(70/99)=224/55.

This is a paper mathematical theorem using the classical
Faber-Krahn inequality, the disk Dirichlet/Bessel relation and
the Bessel derivative formula. The Python receipt verifies every
rational inequality; it does NOT itself typecheck those continuum
PDE or Bessel identities in Agda.
"""
from __future__ import annotations
from fractions import Fraction as F
from math import factorial
import json

X=F(12,5)
A=(X*X)/4
SQRT2_UPPER=F(99,70)
CLAIMED_LOWER=F(224,55)

def bessel_j0_partial(x,degree):
    if degree<0 or degree%2!=1:
        raise ValueError("odd positive degree required for alternating lower bound")
    a=F(x)*F(x)/4
    return sum(((-1)**k * a**k / F(factorial(k)**2)
                for k in range(degree+1)),F(0))

def certificate():
    # Starting at k=1 terms strictly decrease:
    # ratio term(k+1)/term(k)=A/(k+1)^2.
    assert A==F(36,25)
    assert A/F(4)==F(9,25)<1
    lower_at_x=bessel_j0_partial(X,5)
    assert lower_at_x>0
    # J1 inner alternating series ratio <= (36/25)/2=18/25.
    j1_ratio_bound=A/2
    assert j1_ratio_bound==F(18,25)<1
    # 1-x²/8 >= 1-18/25 = 7/25.
    j1_inner_lower=1-A/2
    assert j1_inner_lower==F(7,25)>0
    assert SQRT2_UPPER**2>2
    lower=X**2/SQRT2_UPPER
    assert lower==CLAIMED_LOWER
    return {
        "status":"exact_rational_Faber_Krahn_Gielis_continuum_lower",
        "applies_to_all_positive_integer_modes":True,
        "exact_Gielis_domain_area":"sqrt(2)*pi",
        "J0_first_zero_strictly_greater_than":str(X),
        "J0_alternating_S5_strict_lower_rational":str(lower_at_x),
        "J0_alternating_S5_positive":True,
        "J1_inner_uniform_positive_lower_on_0_to_12_over_5":str(j1_inner_lower),
        "J1_inner_ratio_at_most":str(j1_ratio_bound),
        "sqrt2_strict_rational_upper":str(SQRT2_UPPER),
        "first_continuum_dirichlet_eigenvalue_strict_lower":str(lower),
        "lower_decimal":float(lower),
        "mathematical_donors":["Faber-Krahn","disk Bessel J0 Dirichlet eigenvalue",
                                "J0 derivative = -J1","alternating series"],
        "no_finite_difference_n41_error_claimed":True,
        "native_Agda_Bessel_FaberKrahn_closed":False,
    }

if __name__=="__main__":
    print(json.dumps(certificate(),indent=2,sort_keys=True))
