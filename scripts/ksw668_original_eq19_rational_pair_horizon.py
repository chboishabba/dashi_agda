#!/usr/bin/env python3
"""Exact Fraction finite quadrature of Caldwell-Langlois 2001 Eq19 horizon.

r_g²=(int w sqrt(1+x²))²-(int w x)² and r_ph=(int w),
w=dt/a>0, x=ell H. Rationalize hyperbola with |z|<1:
(A,x)=((1+z²)/(1-z²),2z/(1-z²)).
For any positive rational weights w_i, exact identity:
  r_g²-r_ph² = 4 sum_{i<j} w_i*w_j*(z_i-z_j)² /
                    ((1-z_i²)*(1-z_j²)) >= 0.
Equality for constant H (all z equal). Test refuses negative weights.
Finite quadrature theorem, NOT full real-measure integral or Einstein
solution; see actual original AdS replay in sibling source script.
Original DOI 10.1016/S0370-2693(01)00631-1, Eq19 pp5.
"""
from fractions import Fraction as F
import json

def evaluate(samples):
    if not samples:raise ValueError("Original horizon quadrature needs source")
    for w,z in samples:
        if w<=0 or abs(z)>=1:raise ValueError("Requires w>0, |z|<1")
    I0=sum((w for w,z in samples),F(0))
    I1=sum((w*(1+z*z)/(1-z*z) for w,z in samples),F(0))
    I2=sum((w*2*z/(1-z*z) for w,z in samples),F(0))
    gap=I1*I1-I2*I2-I0*I0
    pair=F(0)
    for j,(wj,zj) in enumerate(samples):
        for wi,zi in samples[:j]:
            pair+=4*wi*wj*(zj-zi)**2/((1-zi*zi)*(1-zj*zj))
    assert gap==pair and gap>=0
    return {"photon_horizon":str(I0),"I1":str(I1),"I2":str(I2),
            "gravity_squared_minus_photon_squared":str(gap),
            "pair_nonnegative_exact":True,"constant_H_iff_zero":gap==0}

def audit():
    variable=evaluate([(F(1),F(0)),(F(1),F(1,3))])
    assert variable["I1"]=="9/4" and variable["I2"]=="3/4"
    assert variable["gravity_squared_minus_photon_squared"]=="1/2"
    const=evaluate([(F(2,3),F(1,3)),(F(3),F(1,3))])
    assert const["gravity_squared_minus_photon_squared"]=="0"
    for n in range(2,15):
        samples=[(F(i+1,n+2),F(i-n//2,2*n+1)) for i in range(n)]
        evaluate(samples)
    try:evaluate([(F(-1),F(0)),(F(1),F(1,3))])
    except ValueError:pass
    else:raise AssertionError("Illegitimate negative source measure accepted")
    return {"status":"PASS exact Fraction pairwise positivity and constant-H equality",
        "original_DOI":"10.1016/S0370-2693(01)00631-1",
        "variable_two_slice":variable,"constant_H_control":const,
        "verified_exact_finite_lengths":"2..14",
        "continuous_measure_Agda_proof":False,
        "physically_sourced_AdS_brane_in_this_script":False}

if __name__=="__main__":
    print(json.dumps(audit(),indent=2,sort_keys=True))
