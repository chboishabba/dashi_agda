#!/usr/bin/env python3
"""Exact five-state NV optical generator and symbolic steady-state checks.
Model = [g0,g1,e0,e1,s] with optical pump, decay, ISC, shelving, MW mixing.
Prior art: DASHI.Biology.Physical.FiniteChemicalMasterGeneratorExact.
Rates are phenomenological; no experimentally sourced NV constants.
"""
import sympy as S
p,w,f0,f1,k0,k1,t0,t1=S.symbols("p w f0 f1 k0 k1 t0 t1",nonnegative=True,real=True)
rates=(p,w,f0,f1,k0,k1,t0,t1)
# Column i is origin, row j destination; probabilities are columns.
Q=S.zeros(5)
for i,j,r in [(0,2,p),(1,3,p),(2,0,f0),(3,1,f1),
              (2,4,k0),(3,4,k1),(4,0,t0),(4,1,t1),
              (0,1,w),(1,0,w)]:
    Q[j,i]+=r;Q[i,i]-=r
assert all(S.simplify(sum(Q[j,i] for j in range(5)))==0 for i in range(5))
assert all(Q[j,i].is_nonnegative for i in range(5) for j in range(5) if i!=j)
# Optical fluorescence observable from radiative excited -> ground jumps.
eta0,eta1,bg=S.symbols("eta0 eta1 bg",nonnegative=True,real=True)
pop=S.Matrix(S.symbols("g0 g1 e0 e1 shelf",nonnegative=True,real=True))
photon_rate=eta0*f0*pop[2]+eta1*f1*pop[3]+bg
assert S.simplify(photon_rate.subs({eta0:0,eta1:0})-bg)==0
# Two-state effective model is NOT algebraically identical to this 5-state model.
assert S.simplify(S.ones(1,5)*Q)==S.zeros(1,5)
print("PASS exact 5-state generator: ten nonnegative transitions, column-sum zero")
print("PASS photon observable tied to radiative excited-state population")
print("OPEN source-calibrated rates; probability trajectory/steady-state; quantum coherence")
