#!/usr/bin/env python3
"""Cross-pollinate canonical DASHI ResponseKink with R4 candidate load envelopes.

Canonical owners (not the utterance module):
  DASHI/Cognition/ResponseKink.agda
  DASHI/Cognition/AnesthesiaLanguagePhaseDynamics.agda
  DASHI/Governance/SituatedHPARegimeFlexibilityExact.agda

The source R4 GELU is NOT by itself overload-suppressing. This audit checks
a rational positive-gain attenuation candidate and an analytically bounded
GELU-times-envelope. No actual trained R4 checkpoint or HPA inference.
"""
import sympy as S
R=S.Rational
passed=[]
def require(label,proposition):
    if not bool(proposition):raise AssertionError("KINK_FAIL "+label)
    passed.append(label)
inputs=tuple(map(R,(0,1,2,3)))
def shape(values):
    return values[0]<values[1]<values[2] and values[3]<values[2]
# Existing original cubic control owner: support=10+4t, impairment=t^3.
cubic=lambda t:10+4*t-t**3
require("original cognitive margin exact 10 13 10 -5",
        tuple(cubic(t) for t in inputs)==(10,13,10,-5))
require("cognitive margin is not the same four-load rising shape",
        not shape([cubic(t) for t in inputs]))
require("original cubic successive changes",
        tuple(cubic(v)-cubic(u) for u,v in zip(inputs[:-1],inputs[1:]))
        ==(3,-3,-15))
# Explicit positive attenuation: this is an analytic candidate,
# NOT a claim that LeechTransformer currently uses it.
attenuation=lambda t:R(16)/(16+t**3)
rational=lambda t:(1+4*t)*attenuation(t)
rvals=tuple(rational(t) for t in inputs)
require("rational four-stage envelope exact values",
        rvals==(1,R(80,17),6,R(208,43)))
require("rational source-profile instantiation has kink shape",
        shape(rvals))
require("attenuation really declines under rising positive load",
        all(attenuation(u)>attenuation(v)
            for u,v in zip(inputs[1:-1],inputs[2:])))
# Original PyTorch nn.GELU() mathematical real target.
Phi=lambda t:(1+S.erf(t/S.sqrt(2)))/2
gelu=lambda t:t*Phi(t)
proposed=lambda t:gelu(t)*attenuation(t)
observed=tuple(proposed(t) for t in inputs)
require("attenuated GELU sampled four-stage shape",
        shape(tuple(float(S.N(z,50)) for z in observed)))
# Rigorous conditional analytic certificate, avoiding a fitted
# float-gate assumption. Phi(2)>7/8 by Mills' normal-tail inequality
# 1-Phi(2)<phi(2)/2<1/8.
phi2=S.exp(-2)/S.sqrt(2*S.pi)
require("normal tail upper bound at 2 below 1/8",
        bool(S.N(phi2/2,60)<S.Rational(1,8)))
require("normal CDF at 2 exceeds 7/8",
        bool(S.N(Phi(2),60)>S.Rational(7,8)))
require("f1 upper < f2 certified lower",
        R(16,17)<R(7,6))
require("f3 upper < f2 certified lower",
        R(48,43)<R(7,6))
require("g(t) alone monotone on t>=0 sample",
        all(float(S.N(gelu(v)-gelu(u),50))>0
            for u,v in zip(inputs[:-1],inputs[1:])))
require("unattenuated GELU cannot supply overload limb",
        not shape(tuple(float(S.N(gelu(t),50)) for t in inputs)))
# Same nominal load can have either shape: no inference about a
# biological state or a specific router from a four-load label alone.
first=(1,4,6,5)
second=(1,2,3,7)
require("identical loads do not determine shape without source observation",
        shape(first) and not shape(second))
# CRITICAL TYPE WELD: the original Agda ResponseKink.response is Nat.
# The rational / analytic real-valued witnesses above are NOT direct
# inhabitants of that type. An order-preserving, calibrated observation
# map is an ADDITIONAL obligation. Here give two finite examples.
nat_rational=tuple(int(S.floor(x)) for x in rvals)
require("Nat observation of rational envelope is still strictly ordered",
        nat_rational==(1,4,6,4) and shape(nat_rational))
nat_gelu=tuple(int(S.floor(10*x)) for x in observed)
require("Nat observation of GELU envelope still meets old shape",
        nat_gelu==(0,7,13,11) and shape(nat_gelu))
# Floor quantization can erase the shape, so the original Nat
# profile cannot be inferred from a real inequality without
# certified separation AFTER the observation map.
erasing=tuple(int(S.floor(x)) for x in observed)
require("unit-scale floor loses strict GELU rise",
        not shape(erasing))
# Rational tail lower bound improved to Phi(2)>15/16:
# thus a(2)> (2*15/16)*(2/3) = 5/4;
# with scale 10, floor(10*a2) >=12.
# At a3<=48/43, floor(10*a3)<=11.
require("tail-bound supports robust Nat peak vs overload",
        bool(S.N(phi2/2,60)<R(1,16)) and R(5,4)>R(48,43))
require("Nat scale10 stage1 and peak separation certified",
        R(10)*R(16,17)<R(10)*R(5,4))

print("X369_EARLY_KINK_CROSSWALK_SYMPY_PASS",len(passed))
print("EXACT_RATIONAL_ENVELOPE",rvals,"Nat",nat_rational)
print("GELU_ENVELOPE",tuple(str(S.N(z,12)) for z in observed),"Nat",nat_gelu)
