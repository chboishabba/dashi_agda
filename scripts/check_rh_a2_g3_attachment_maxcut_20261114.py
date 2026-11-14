#!/usr/bin/env python3
"""Exact Fraction negative controls for the attached RH A2/G3 arguments.

NOT a certificate about original selected zeta-zero FarExact, nor about
original Lean Route-B signedFifthCorrelationGapAt (physical cap+outer-3eps).
"""
import json
from fractions import Fraction as Q

def pole(a,b):
    return (a*a-b*b)/(a*a+b*b)**2

def signed(x,y,a,b,mu1,mu2):
    m=(a*x*x+b*y*y)/(a+b)
    return mu1*a*(x**5-m*x**3)+mu2*b*(y**5-m*y**3)

def check():
    assert pole(Q(1,4),Q(1,2))==Q(-48,25)
    assert pole(Q(1,4),Q(1))==Q(-240,289)
    far=0
    for p in (1,2,3,5,7):
        for q in (2,4,8,16):
            a=Q(p,q)
            for b in (Q(1),Q(5,4),Q(3,2),Q(2),Q(4)):
                if a<=Q(1,2):
                    assert pole(a,b)<0
                    far+=1
    pairs=0
    for x,y in ((Q(1),Q(2)),(Q(3,2),Q(7,4)),
                (Q(14),Q(21)),(Q(14134725,1000000),Q(21022040,1000000))):
        for a,b in ((Q(1),Q(1)),(Q(1),Q(1024)),
                    (Q(1024),Q(1)),(Q(17,1000),Q(1,1000000))):
            minus=-a*b/(a+b)*(y*y-x*x)*(x**3+y**3)
            plus=a*b/(a+b)*(y*y-x*x)*(y**3-x**3)
            assert signed(x,y,a,b,1,-1)==minus<0
            assert signed(x,y,a,b,1,1)==plus>0
            pairs+=1
    assert Q(28416,25)>Q(7374,10)
    return {
      "schema":"rh-a2-g3-attachment-exact-negative-controls-v1",
      "result":"PASS","near_pole_curvature":"-48/25",
      "near_horizontal":"1/4","near_vertical":"1/2",
      "local_positive_floor_claim_fails":True,
      "far_pole_curvature":"-240/289",
      "far_curvature_negative_checks":far,
      "two_mode_sign_checks":pairs,
      "mu_plus_minus_identity":"-a*b/(a+b)*(y^2-x^2)*(x^3+y^3)",
      "proposed_bump_K":"28416/25",
      "original_A2_W_fourthLipschitz_certified":False,
      "original_A2_signed_compensation_or_no_go_closed":False,
      "original_RouteB_gap_identified_with_heat_surrogate":False,
      "RH_G3_closed":False,"Lean_kernel_receipt":False}

if __name__=="__main__":
    print(json.dumps(check(),indent=2))
